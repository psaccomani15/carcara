use super::{assert_clause_len, assert_eq, assert_num_args, RuleArgs, RuleResult};
use crate::{
    ast::{Operator, Rc, Sort, Term},
    checker::{
        error::{CheckerError, PolynomialError},
        rules::polynomial::ff_poly_norm_eq,
    },
};
use indexmap::IndexSet;
use rug::Integer;

/// Collects the atomic terms of a polynomial — the terms that the polynomial
/// normalizer treats as opaque leaves (variables, choice/skolem terms, etc.).
/// This mirrors the dispatch logic of `Polynomial::add_term`.
fn collect_poly_atoms(term: &Rc<Term>, atoms: &mut IndexSet<Rc<Term>>) {
    match term.as_ref() {
        Term::Op(Operator::FfAdd, args) => {
            for a in args {
                collect_poly_atoms(a, atoms);
            }
        }
        Term::Op(Operator::FfNeg, args) if args.len() == 1 => {
            collect_poly_atoms(&args[0], atoms);
        }
        Term::Op(Operator::FfMul, args) => {
            for a in args {
                collect_poly_atoms(a, atoms);
            }
        }
        _ => {
            if term.as_ffval().is_none() {
                atoms.insert(term.clone());
            }
        }
    }
}

/// Extracts the literals from a conjunction. If the term is not a conjunction,
/// returns a single-element vec.
fn extract_literals(term: &Rc<Term>) -> Vec<&Rc<Term>> {
    match term.as_ref() {
        Term::Op(Operator::And, args) => args.iter().collect(),
        _ => vec![term],
    }
}

/// Extracts the ideal generators from a term of the form
/// `(not (set.is_empty (@ff.variety (@ff.ideal g1 ... gn))))`.
fn extract_ideal_generators(term: &Rc<Term>) -> Option<&[Rc<Term>]> {
    let inner = match_term!((not t) = term)?;
    match inner.as_ref() {
        Term::Op(Operator::SetIsEmpty, args) if args.len() == 1 => match args[0].as_ref() {
            Term::Op(Operator::FfVariety, vargs) if vargs.len() == 1 => match vargs[0].as_ref() {
                Term::Op(Operator::FfIdeal, generators) => Some(generators.as_slice()),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

pub fn ff_poly_conversion(RuleArgs { conclusion, args, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    assert_num_args(&args, 2)?;

    let (lhs, rhs) = match_term_err!((= t s) = &conclusion[0])?;

    assert_eq(lhs, &args[0])?;
    assert_eq(rhs, &args[1])?;

    let generators = extract_ideal_generators(rhs).ok_or_else(|| {
        CheckerError::TermOfWrongForm(
            "(not (set.is_empty (@ff.variety (@ff.ideal ...))))",
            rhs.clone(),
        )
    })?;

    let literals = extract_literals(lhs);

    if literals.len() != generators.len() {
        return Err(CheckerError::WrongNumberOfTermsInOp(
            Operator::And,
            literals.len().into(),
            generators.len(),
        ));
    }

    let order = match pool.sort(&generators[0]).as_sort().unwrap() {
        Sort::Ff(order) => order.clone(),
        other => return Err(PolynomialError::ExpectedFfSort(other.clone()).into()),
    };

    for (literal, generator) in literals.iter().zip(generators.iter()) {
        if let Some((a, b)) = match_term!((= a b) = literal) {
            // Equality (= a b): generator normalizes to b - a
            let neg_a = pool.add(Term::Op(Operator::FfNeg, vec![a.clone()]));
            let diff = pool.add(Term::Op(Operator::FfAdd, vec![b.clone(), neg_a]));
            ff_poly_norm_eq(generator, &diff, &order)?;
        } else if let Some((a, b)) = match_term!((not (= a b)) = literal) {
            // Disequality (not (= a b)): generator is (a - b) * d + (p - 1)
            // Find the Skolem d: polynomial atom in generator not in a or b
            let mut gen_atoms = IndexSet::new();
            collect_poly_atoms(generator, &mut gen_atoms);
            let mut ab_atoms = IndexSet::new();
            collect_poly_atoms(a, &mut ab_atoms);
            collect_poly_atoms(b, &mut ab_atoms);

            let fresh: Vec<_> = gen_atoms.difference(&ab_atoms).collect();
            if fresh.len() != 1 {
                return Err(CheckerError::TermOfWrongForm(
                    "disequality generator with exactly one fresh variable",
                    generator.clone(),
                ));
            }
            let d = fresh[0];

            // Build expected: (a - b) * d + (p - 1)
            let neg_b = pool.add(Term::Op(Operator::FfNeg, vec![b.clone()]));
            let diff = pool.add(Term::Op(Operator::FfAdd, vec![a.clone(), neg_b]));
            let product = pool.add(Term::Op(Operator::FfMul, vec![diff, d.clone()]));
            let p_minus_1 =
                pool.add(Term::new_ffval(Integer::from(&order - 1u32), order.clone()));
            let expected = pool.add(Term::Op(Operator::FfAdd, vec![product, p_minus_1]));

            ff_poly_norm_eq(generator, &expected, &order)?;
        } else {
            return Err(CheckerError::TermOfWrongForm(
                "(= a b) or (not (= a b))",
                (*literal).clone(),
            ));
        }
    }

    Ok(())
}
