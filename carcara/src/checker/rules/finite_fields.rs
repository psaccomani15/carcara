use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, get_premise_term,
    RuleArgs, RuleResult,
};
use crate::{
    ast::{Operator, Rc, Sort, Term},
    checker::error::{CheckerError, PolynomialError},
};
use rug::Integer;
use std::{
    env, fs,
    io::Write,
    path::PathBuf,
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
};

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

/// Verifies an `ff_poly_conversion` step.
///
/// Premise: a term of the form `(and (= p1 #f0) ... (= pn #f0))` (or a single
/// `(= p #f0)` when there is only one literal). Conclusion clause:
/// `(not (set.is_empty (@ff.variety (@ff.ideal p1 ... pn))))`.
///
/// The rule checks that each ideal generator `pi` matches the left-hand side of
/// the i-th conjunct in the premise and that every right-hand side is the
/// finite field zero.
pub fn ff_poly_conversion(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    assert_num_premises(premises, 1)?;

    let generators = extract_ideal_generators(&conclusion[0]).ok_or_else(|| {
        CheckerError::TermOfWrongForm(
            "(not (set.is_empty (@ff.variety (@ff.ideal ...))))",
            conclusion[0].clone(),
        )
    })?;

    let premise = get_premise_term(&premises[0])?;
    let eqs: Vec<&Rc<Term>> = match premise.as_ref() {
        Term::Op(Operator::And, conjuncts) => conjuncts.iter().collect(),
        _ => vec![premise],
    };

    if eqs.len() != generators.len() {
        return Err(CheckerError::WrongNumberOfTermsInOp(
            Operator::And,
            generators.len().into(),
            eqs.len(),
        ));
    }

    for (eq, generator) in eqs.iter().zip(generators.iter()) {
        let (lhs, rhs) = match_term_err!((= p z) = *eq)?;
        let (val, _) = rhs.as_ffval().ok_or_else(|| {
            CheckerError::TermOfWrongForm("finite field zero constant", rhs.clone())
        })?;
        if val != 0 {
            return Err(CheckerError::TermOfWrongForm(
                "(= pi #f0)",
                (*eq).clone(),
            ));
        }
        assert_eq(lhs, generator)?;
    }

    Ok(())
}

/// Verifies an `ff_diseq` step.
///
/// Given `:args (l r sk)`, the conclusion clause must be
/// `(= (not (= l r)) (= (ff.add (ff.mul (ff.add l (ff.neg r)) sk) #f(p-1)m<p>) #f0m<p>))`,
/// where `p` is the order of the finite field `l` lives in.
pub fn ff_diseq(RuleArgs { conclusion, args, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    assert_num_args(args, 3)?;

    let l = &args[0];
    let r = &args[1];
    let sk = &args[2];

    let order = match pool.sort(l).as_sort().unwrap() {
        Sort::Ff(order) => order.clone(),
        other => return Err(PolynomialError::ExpectedFfSort(other.clone()).into()),
    };

    let neg_r = pool.add(Term::Op(Operator::FfNeg, vec![r.clone()]));
    let sub = pool.add(Term::Op(Operator::FfAdd, vec![l.clone(), neg_r]));
    let prod = pool.add(Term::Op(Operator::FfMul, vec![sub, sk.clone()]));
    let minus_one =
        pool.add(Term::new_ffval(Integer::from(&order - 1u32), order.clone()));
    let witness = pool.add(Term::Op(Operator::FfAdd, vec![prod, minus_one]));
    let zero = pool.add(Term::new_ffval(0, order.clone()));
    let witness_eq = pool.add(Term::Op(Operator::Equals, vec![witness, zero]));
    let lr_eq = pool.add(Term::Op(Operator::Equals, vec![l.clone(), r.clone()]));
    let not_lr_eq = pool.add(Term::Op(Operator::Not, vec![lr_eq]));
    let expected = pool.add(Term::Op(Operator::Equals, vec![not_lr_eq, witness_eq]));

    assert_eq(&conclusion[0], &expected)?;
    Ok(())
}

/// Ensures a file is removed when this guard is dropped, so a failure during
/// solver invocation does not leak the temporary certificate file.
struct TempFileGuard(PathBuf);

impl Drop for TempFileGuard {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn ff_pac_temp_path() -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    env::temp_dir().join(format!("carcara-ff-pac-{}-{}.pac", std::process::id(), n))
}

/// Checks an `ff_pac` step by invoking the external `ffpacheck` binary.
/// The proof certificate is written to a temporary file which is passed to the
/// checker as its single argument.
pub fn check_ff_pac(args: &[Rc<Term>], solver_path: &str) -> RuleResult {
    use crate::ast::Constant;

    let first_arg = args.first().ok_or_else(|| CheckerError::Unspecified)?;

    let proof_str = match first_arg.as_ref() {
        Term::Const(Constant::String(s)) => s,
        _ => {
            return Err(CheckerError::TermOfWrongForm(
                "ff_pac proof certificate string",
                first_arg.clone(),
            ));
        }
    };

    let path = ff_pac_temp_path();
    let _guard = TempFileGuard(path.clone());
    {
        let mut file = fs::File::create(&path).map_err(CheckerError::FfPacSpawnError)?;
        file.write_all(proof_str.as_bytes())
            .map_err(CheckerError::FfPacSpawnError)?;
    }

    let status = Command::new(solver_path)
        .arg(&path)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map_err(CheckerError::FfPacSpawnError)?;

    if !status.success() {
        return Err(CheckerError::FfPacFailed(status.code()));
    }

    Ok(())
}
