//! Rules of the univariate coverings calculus, used by cvc5 to justify conflicts found by its
//! cylindrical algebraic coverings procedure.
use super::{
    RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_is_bool_constant,
    assert_is_expected, assert_num_args, assert_num_premises, get_premise_term,
    polynomial::{
        Polynomial, UPoly, upoly_add, upoly_derivative, upoly_divides, upoly_eval,
        upoly_leading_coeff, upoly_mul, upoly_scale, upoly_sign_at_inf, upoly_sub,
    },
};
use crate::{
    ast::{
        Constant, Operator, Rc, RealAlgebraicNumberWitness, Term, build_term, match_term,
        match_term_err, pool::Pool,
    },
    checker::error::{CheckerError, CoveringsError},
};
use rug::Rational;
use std::collections::{HashMap, hash_map::Entry};

/// A signed remainder sequence as shipped by cvc5: each element comes with the pseudo-quotient of
/// the division that produced it (zero for the first two elements).
type RemainderSequence = Vec<(UPoly, UPoly)>;

/// The maximum number of times the isolating intervals of two endpoints are halved while trying to
/// decide their order.
const MAX_REFINEMENTS: usize = 256;

/// A real algebraic number witness that was checked to be well defined (see `validate_witness`).
struct ValidWitness {
    /// The defining polynomial.
    poly: UPoly,

    /// The Sturm sequence of the defining polynomial.
    sturm: RemainderSequence,
}

/// The real algebraic number witnesses validated so far, so that each is validated only once
/// even if it occurs in many steps. Since the variable over which a witness is validated only
/// names the indeterminate of its polynomials, witnesses are identified by their terms alone.
#[derive(Default)]
pub struct WitnessCache(HashMap<Rc<Term>, ValidWitness>);

impl WitnessCache {
    /// Validates the witness `witness`, given by the term `term`, over the variable `var`, unless
    /// it was validated before.
    fn validate(
        &mut self,
        term: &Rc<Term>,
        witness: &RealAlgebraicNumberWitness,
        var: &Rc<Term>,
    ) -> Result<&ValidWitness, CoveringsError> {
        Ok(match self.0.entry(term.clone()) {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(validate_witness(witness, var)?),
        })
    }
}

/// Tries to extract a real algebraic number witness from a term.
fn as_ran_witness(term: &Rc<Term>) -> Option<&RealAlgebraicNumberWitness> {
    match term.as_ref() {
        Term::Const(Constant::RealAlgebraicWitness(w)) => Some(w),
        _ => None,
    }
}

fn is_minus_inf(term: &Rc<Term>) -> bool {
    matches!(term.as_ref(), Term::Op(Operator::CovMinusInf, _))
}

fn is_plus_inf(term: &Rc<Term>) -> bool {
    matches!(term.as_ref(), Term::Op(Operator::CovPlusInf, _))
}

/// Returns `true` if the term is one of the infinity markers, `@cov_minus_inf` or
/// `@cov_plus_inf`.
fn is_infinite(term: &Rc<Term>) -> bool {
    is_minus_inf(term) || is_plus_inf(term)
}

/// An interval containing the value of a finite endpoint: the point `[r, r]` for a rational `r`,
/// or the isolating interval of a real algebraic number witness, which can be refined.
struct EndpointBounds<'a> {
    lower: Rational,
    upper: Rational,
    witness: Option<&'a ValidWitness>,
}

impl<'a> EndpointBounds<'a> {
    /// Returns the bounds of a finite endpoint, which must have been validated if it is a witness.
    fn new(witnesses: &'a WitnessCache, term: &Rc<Term>) -> Result<Self, CoveringsError> {
        let invalid = || CoveringsError::InvalidEndpoint(term.clone());
        if let Some(r) = term.as_fraction() {
            Ok(Self {
                lower: r.clone(),
                upper: r,
                witness: None,
            })
        } else {
            let w = as_ran_witness(term).ok_or_else(invalid)?;
            Ok(Self {
                lower: w.ran.lower.clone(),
                upper: w.ran.upper.clone(),
                witness: Some(witnesses.0.get(term).ok_or_else(invalid)?),
            })
        }
    }

    fn is_point(&self) -> bool {
        self.lower == self.upper
    }

    /// Halves the isolating interval of a witness, keeping the half that contains its root. The
    /// half is found by counting roots with the Sturm sequence, since the defining polynomial may
    /// not change sign at a root of even multiplicity.
    fn refine(&mut self) {
        let Some(witness) = self.witness else {
            return;
        };
        if self.is_point() {
            return;
        }
        let mid = Rational::from(&self.lower + &self.upper) / 2;
        if upoly_eval(&witness.poly, &mid).is_zero() {
            self.lower = mid.clone();
            self.upper = mid;
        } else if sign_variations_at(&witness.sturm, &self.lower)
            - sign_variations_at(&witness.sturm, &mid)
            == 1
        {
            self.upper = mid;
        } else {
            self.lower = mid;
        }
    }
}

/// Decides whether `a < b`, for two interval endpoints, whose witnesses must have been validated.
/// Real algebraic numbers are compared using their isolating intervals, which are refined while
/// they overlap. If they still overlap after `MAX_REFINEMENTS` refinements, as happens for two
/// distinct witnesses of the same number, an error is returned.
fn endpoint_lt(
    witnesses: &WitnessCache,
    a: &Rc<Term>,
    b: &Rc<Term>,
) -> Result<bool, CoveringsError> {
    if a == b {
        return Ok(false);
    }
    if is_minus_inf(a) || is_plus_inf(b) {
        return Ok(true);
    }
    if is_plus_inf(a) || is_minus_inf(b) {
        return Ok(false);
    }
    let mut a_bounds = EndpointBounds::new(witnesses, a)?;
    let mut b_bounds = EndpointBounds::new(witnesses, b)?;

    for _ in 0..=MAX_REFINEMENTS {
        // The value of a witness whose interval is not a point lies strictly inside it, so when
        // the intervals only touch, the endpoints are equal only if both are points
        let both_points = a_bounds.is_point() && b_bounds.is_point();
        if a_bounds.upper < b_bounds.lower || (a_bounds.upper == b_bounds.lower && !both_points) {
            return Ok(true);
        }
        if b_bounds.upper <= a_bounds.lower {
            return Ok(false);
        }
        a_bounds.refine();
        b_bounds.refine();
    }
    Err(CoveringsError::IncomparableEndpoints(a.clone(), b.clone()))
}

/// Converts a term into a univariate polynomial over `var`.
fn term_to_upoly(term: &Rc<Term>, var: &Rc<Term>) -> Result<UPoly, CoveringsError> {
    Polynomial::from_term(term)
        .to_univariate(var)
        .ok_or_else(|| CoveringsError::NotUnivariate(term.clone(), var.clone()))
}

/// Converts a sequence of `(quotient, polynomial)` term pairs into univariate polynomials over
/// `var`.
fn terms_to_sequence(
    pairs: &[(Rc<Term>, Rc<Term>)],
    var: &Rc<Term>,
) -> Result<RemainderSequence, CoveringsError> {
    pairs
        .iter()
        .map(|(q, p)| Ok((term_to_upoly(q, var)?, term_to_upoly(p, var)?)))
        .collect()
}

/// Counts the sign variations of a sequence of polynomials, each evaluated to a sign by `sign`,
/// ignoring zeros.
fn sign_variations(seq: &RemainderSequence, sign: impl Fn(&[Rational]) -> i32) -> i64 {
    let mut variations = 0;
    let mut last = 0;
    for s in seq.iter().map(|(_, p)| sign(p)).filter(|s| *s != 0) {
        if last != 0 && s != last {
            variations += 1;
        }
        last = s;
    }
    variations
}

fn sign_variations_at(seq: &RemainderSequence, x: &Rational) -> i64 {
    sign_variations(seq, |p| upoly_eval(p, x).cmp0() as i32)
}

fn sign_variations_at_inf(seq: &RemainderSequence, positive: bool) -> i64 {
    sign_variations(seq, |p| upoly_sign_at_inf(p, positive))
}

/// Checks that `seq` is the signed remainder sequence that starts with `first` and `second`, up
/// to constant factors, using the shipped pseudo-quotients.
fn check_remainder_sequence(
    seq: &RemainderSequence,
    first: &[Rational],
    second: &[Rational],
) -> Result<(), CoveringsError> {
    let elements: Vec<&UPoly> = seq.iter().map(|(_, p)| p).collect();
    let n = elements.len() - usize::from(elements.last().is_some_and(|p| p.is_empty()));
    if n < 2 {
        return Err(CoveringsError::RemainderSequenceTooShort(n));
    }
    if elements[..n].iter().any(|p| p.is_empty()) || first.is_empty() || second.is_empty() {
        return Err(CoveringsError::InvalidRemainderSequence(0));
    }

    let c0 = upoly_leading_coeff(elements[0]) / upoly_leading_coeff(first);
    let c1 = upoly_leading_coeff(elements[1]) / upoly_leading_coeff(second);
    if *elements[0] != upoly_scale(&c0, first) {
        return Err(CoveringsError::InvalidRemainderSequence(0));
    }
    if *elements[1] != upoly_scale(&c1, second) || !Rational::from(&c0 * &c1).is_positive() {
        return Err(CoveringsError::InvalidRemainderSequence(1));
    }

    for i in 2..n {
        let (a, b, c) = (elements[i - 2], elements[i - 1], elements[i]);
        let quotient = &seq[i].0;
        // `m` makes the leading terms of `m * a` and `q * b` cancel; when the degree of `a` is
        // lower than that of `b`, the quotient is zero and the remainder is `a` itself
        let m = if quotient.is_empty() {
            Rational::from(1)
        } else {
            upoly_leading_coeff(quotient) * upoly_leading_coeff(b) / upoly_leading_coeff(a)
        };
        let rem = upoly_sub(&upoly_scale(&m, a), &upoly_mul(quotient, b));
        if rem.len() >= b.len() || rem.len() != c.len() {
            return Err(CoveringsError::InvalidRemainderSequence(i));
        }
        let k = -(upoly_leading_coeff(&rem) / upoly_leading_coeff(c));
        if !Rational::from(&m * &k).is_positive()
            || !upoly_add(&rem, &upoly_scale(&k, c)).is_empty()
        {
            return Err(CoveringsError::InvalidRemainderSequence(i));
        }
    }

    if upoly_divides(elements[n - 1], elements[n - 2]) {
        Ok(())
    } else {
        Err(CoveringsError::IncompleteRemainderSequence)
    }
}

/// Checks that `seq` is a Sturm sequence of `p`, that is, the signed remainder sequence of `p` and
/// its derivative.
fn check_sturm_sequence(seq: &RemainderSequence, p: &[Rational]) -> Result<(), CoveringsError> {
    check_remainder_sequence(seq, p, &upoly_derivative(p))
}

/// Checks that a witness is well defined: its Sturm sequence is a Sturm sequence of its defining
/// polynomial `q`, which is nonzero at the bounds of its isolating interval and has exactly one
/// root inside it. This is done through `WitnessCache::validate`, so that each witness is
/// validated only once.
fn validate_witness(
    witness: &RealAlgebraicNumberWitness,
    var: &Rc<Term>,
) -> Result<ValidWitness, CoveringsError> {
    let q = term_to_upoly(&witness.ran.poly, var)?;
    if q.is_empty() {
        return Err(CoveringsError::ZeroPolynomial(witness.ran.poly.clone()));
    }
    let seq = terms_to_sequence(&witness.sturm, var)?;
    check_sturm_sequence(&seq, &q)?;
    for bound in [&witness.ran.lower, &witness.ran.upper] {
        if upoly_eval(&q, bound).is_zero() {
            return Err(CoveringsError::RootAtBound(bound.clone()));
        }
    }
    let roots =
        sign_variations_at(&seq, &witness.ran.lower) - sign_variations_at(&seq, &witness.ran.upper);
    if roots != 1 {
        return Err(CoveringsError::WrongNumberOfRoots(roots));
    }
    Ok(ValidWitness { poly: q, sturm: seq })
}

/// Computes the Tarski query of a signed remainder sequence of `(q, q' * p)` on the interval
/// `(lower, upper)`, where `q` is nonzero at both bounds: the sum of the signs of `p` at the roots
/// of `q` in the interval. On the isolating interval of a witness with defining polynomial `q`,
/// this is the sign of `p` at the witness.
fn tarski_query(seq: &RemainderSequence, lower: &Rational, upper: &Rational) -> i64 {
    sign_variations_at(seq, lower) - sign_variations_at(seq, upper)
}

fn expect_variable(term: &Rc<Term>) -> Result<(), CoveringsError> {
    if term.is_var() {
        Ok(())
    } else {
        Err(CoveringsError::ExpectedVariable(term.clone()))
    }
}

/// Checks that a term is a valid interval endpoint: a rational constant, an infinity marker, or a
/// well defined real algebraic number witness, over the variable `var`.
fn validate_endpoint(
    witnesses: &mut WitnessCache,
    term: &Rc<Term>,
    var: &Rc<Term>,
) -> Result<(), CoveringsError> {
    if let Some(witness) = as_ran_witness(term) {
        witnesses.validate(term, witness, var)?;
    } else if term.as_fraction().is_none() && !is_infinite(term) {
        return Err(CoveringsError::InvalidEndpoint(term.clone()));
    }
    Ok(())
}

/// Evaluates the polynomial term `p`, over the variable `var`, at the rational `x`.
fn eval_at(p: &Rc<Term>, var: &Rc<Term>, x: &Rational) -> Result<Rational, CoveringsError> {
    Ok(upoly_eval(&term_to_upoly(p, var)?, x))
}

/// Destructures a literal `(~ p 0)` or `(not (~ p 0))`, where `~` is a comparison operator, into
/// the operator, whether the literal is negated, and `p`.
fn as_literal(term: &Rc<Term>) -> Result<(Operator, bool, &Rc<Term>), CoveringsError> {
    let (negated, atom) = match match_term!((not a) = term) {
        Some(a) => (true, a),
        None => (false, term),
    };
    match atom.as_op() {
        Some((
            op @ (Operator::Equals
            | Operator::LessThan
            | Operator::GreaterThan
            | Operator::LessEq
            | Operator::GreaterEq),
            [p, zero],
        )) if zero.as_fraction().is_some_and(|z| z.is_zero()) => Ok((op, negated, p)),
        _ => Err(CoveringsError::InvalidLiteral(term.clone())),
    }
}

/// Returns whether a literal `(~ p 0)`, or `(not (~ p 0))` if `negated`, holds when `p` evaluates
/// to `value`.
fn literal_holds(op: Operator, negated: bool, value: &Rational) -> bool {
    let holds = match op {
        Operator::Equals => value.is_zero(),
        Operator::LessThan => value.is_negative(),
        Operator::GreaterThan => value.is_positive(),
        Operator::LessEq => !value.is_positive(),
        Operator::GreaterEq => !value.is_negative(),
        _ => unreachable!(),
    };
    holds != negated
}

/// Builds the term stating that `x` is in the open interval `(l, r)`, omitting the conjunct of an
/// infinite endpoint. Returns `None` for the whole line.
fn open_piece(pool: &mut Pool, x: &Rc<Term>, l: &Rc<Term>, r: &Rc<Term>) -> Option<Rc<Term>> {
    let lower = (!is_minus_inf(l)).then(|| build_term!(pool, (> {x.clone()} {l.clone()})));
    let upper = (!is_plus_inf(r)).then(|| build_term!(pool, (< {x.clone()} {r.clone()})));
    match (lower, upper) {
        (Some(lower), Some(upper)) => Some(build_term!(pool, (and {lower} {upper}))),
        (Some(piece), None) | (None, Some(piece)) => Some(piece),
        (None, None) => None,
    }
}

/// The `cover` rule: given a variable `x` and intervals `(l1, u1) ... (ln, un)`, whose union is
/// the whole real line, concludes that `x` is in one of them. A point interval `(c, c)` gives the
/// literal `(= x c)`, and an open one `(l, u)` gives `(and (> x l) (< x u))`, without the
/// conjunct of an infinite endpoint.
///
/// To check that the intervals cover the line, we sweep them in the given order while keeping
/// track of the covered prefix of the line, `(-inf, f)` or `(-inf, f]`: an open interval must
/// start inside the prefix, and extends it if it ends after it; a point interval ending the
/// prefix closes it. At the end, the prefix must be the whole line. This is a sufficient
/// condition, which the intervals generated by cvc5 satisfy.
pub fn cover(
    RuleArgs {
        conclusion, args, pool, witnesses, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_args(args, 3..)?;
    let x = &args[0];
    expect_variable(x)?;
    let endpoints = &args[1..];
    rassert!(
        endpoints.len().is_multiple_of(2),
        CoveringsError::WrongNumberOfEndpoints(endpoints.len()),
    );
    let intervals: Vec<_> = endpoints.chunks_exact(2).map(|c| (&c[0], &c[1])).collect();
    assert_clause_len(conclusion, intervals.len())?;

    for (&(l, u), literal) in intervals.iter().zip(conclusion) {
        validate_endpoint(witnesses, l, x)?;
        validate_endpoint(witnesses, u, x)?;
        let expected = if l == u {
            rassert!(
                !is_infinite(l),
                CoveringsError::InvalidInterval(l.clone(), u.clone())
            );
            build_term!(pool, (= {x.clone()} {l.clone()}))
        } else {
            open_piece(pool, x, l, u)
                .ok_or_else(|| CoveringsError::InvalidInterval(l.clone(), u.clone()))?
        };
        assert_is_expected(literal, expected)?;
    }

    // `frontier` is the end of the covered prefix, which includes it if `frontier_covered`
    let mut frontier = pool.add(Term::Op(Operator::CovMinusInf, Vec::new()));
    let mut frontier_covered = true;
    for &(l, u) in &intervals {
        if l == u {
            if *l == frontier {
                frontier_covered = true;
            } else if endpoint_lt(witnesses, &frontier, l)? {
                return Err(CoveringsError::CoverGap(frontier, l.clone()).into());
            }
        } else {
            let attaches =
                endpoint_lt(witnesses, l, &frontier)? || (*l == frontier && frontier_covered);
            rassert!(
                attaches,
                CoveringsError::CoverGap(frontier.clone(), l.clone())
            );
            if endpoint_lt(witnesses, &frontier, u)? {
                frontier = u.clone();
                frontier_covered = false;
            }
        }
    }
    rassert!(
        is_plus_inf(&frontier),
        CoveringsError::CoverIncomplete(frontier)
    );
    Ok(())
}

/// Returns the only variable of a polynomial term.
fn poly_variable(pool: &mut Pool, p: &Rc<Term>) -> Result<Rc<Term>, CoveringsError> {
    match pool.free_vars(p).iter().collect::<Vec<_>>().as_slice() {
        [var] => Ok((*var).clone()),
        _ => Err(CoveringsError::ExpectedOneVariable(p.clone())),
    }
}

/// Groups the terms of a flattened sequence of pairs `a1 b1 ... an bn`.
fn as_pairs(terms: &[Rc<Term>]) -> Result<Vec<(Rc<Term>, Rc<Term>)>, CoveringsError> {
    if !terms.len().is_multiple_of(2) {
        return Err(CoveringsError::OddSequenceLength(terms.len()));
    }
    Ok(terms
        .chunks_exact(2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect())
}

/// Reads a sequence of pairs preceded by its number of pairs from the start of `args`, returning
/// the pairs and the remaining arguments.
fn take_counted_pairs(
    args: &[Rc<Term>],
) -> Result<(Vec<(Rc<Term>, Rc<Term>)>, &[Rc<Term>]), CheckerError> {
    let count = args
        .first()
        .ok_or(CheckerError::WrongNumberOfArgs(1.into(), 0))?;
    let count = count
        .as_fraction()
        .filter(|c| c.is_integer() && !c.is_negative())
        .and_then(|c| c.numer().to_usize())
        .ok_or_else(|| CheckerError::ExpectedNonnegInteger(count.clone()))?;
    let len = 2 * count;
    if args.len() < len + 1 {
        return Err(CheckerError::WrongNumberOfArgs(
            (len + 1).into(),
            args.len(),
        ));
    }
    Ok((as_pairs(&args[1..=len])?, &args[len + 1..]))
}

/// Checks that the endpoint `r` is a root of the polynomial `p` (over `var`, with coefficients
/// `p_coeffs`), given the Sturm-Tarski sequence of `(q, q' * p)` for a witness `r` with defining
/// polynomial `q`, whose Tarski query on the isolating interval of `r` must be zero. If `q`
/// divides `p`, `r` is a root of `p` regardless, and the sequence is ignored. A rational `r` is
/// checked by evaluation, and must come with no sequence.
fn check_root(
    witnesses: &mut WitnessCache,
    p: &Rc<Term>,
    p_coeffs: &[Rational],
    r: &Rc<Term>,
    sequence: &[(Rc<Term>, Rc<Term>)],
    var: &Rc<Term>,
) -> Result<(), CoveringsError> {
    if let Some(witness) = as_ran_witness(r) {
        let q = &witnesses.validate(r, witness, var)?.poly;
        if upoly_divides(q, p_coeffs) {
            return Ok(());
        }
        let seq = terms_to_sequence(sequence, var)?;
        check_remainder_sequence(&seq, q, &upoly_mul(&upoly_derivative(q), p_coeffs))?;
        if tarski_query(&seq, &witness.ran.lower, &witness.ran.upper) != 0 {
            return Err(CoveringsError::NotRoot(p.clone(), r.clone()));
        }
    } else {
        let value = r
            .as_fraction()
            .ok_or_else(|| CoveringsError::InvalidEndpoint(r.clone()))?;
        if !sequence.is_empty() {
            return Err(CoveringsError::UnexpectedSequence(r.clone()));
        }
        if !upoly_eval(p_coeffs, &value).is_zero() {
            return Err(CoveringsError::NotRoot(p.clone(), r.clone()));
        }
    }
    Ok(())
}

/// Checks the window bound `bound` of the endpoint `endpoint`, on the side `below` of it: the
/// bound must be the same infinity marker if the endpoint is infinite, and otherwise a rational
/// strictly below (or above) the endpoint which is not a root of the polynomial. The endpoint
/// must have been validated. Returns the value of a finite bound.
fn check_window_bound(
    witnesses: &WitnessCache,
    p_coeffs: &[Rational],
    endpoint: &Rc<Term>,
    bound: &Rc<Term>,
    below: bool,
) -> Result<Option<Rational>, CoveringsError> {
    let invalid = || CoveringsError::InvalidWindowBound(bound.clone(), endpoint.clone());
    if is_infinite(endpoint) {
        return if bound == endpoint {
            Ok(None)
        } else {
            Err(invalid())
        };
    }
    let value = bound.as_fraction().ok_or_else(invalid)?;
    let (lower, upper) = if below {
        (bound, endpoint)
    } else {
        (endpoint, bound)
    };
    if !endpoint_lt(witnesses, lower, upper)? {
        return Err(invalid());
    }
    if upoly_eval(p_coeffs, &value).is_zero() {
        return Err(CoveringsError::WindowBoundIsRoot(bound.clone()));
    }
    Ok(Some(value))
}

/// The `sgn_inv_intro` rule: concludes `(@sgn_inv p l r)`, that is, that the polynomial `p` has
/// a constant sign on the open interval `(l, r)`, from the arguments `p l r lo hi` followed by
/// three counted sequences of pairs: the Sturm sequence of `p`, and the Sturm-Tarski sequences
/// showing that `l` and `r` are roots of `p` (empty for a rational or infinite endpoint). The
/// window `(lo, hi)` is given by rational bounds around the interval, or by the same infinity
/// markers, at which `p` is nonzero. Since `p` has as many roots in the window as the interval
/// has finite endpoints, which are both roots, it has no roots in the interval.
pub fn sgn_inv_intro(
    RuleArgs {
        conclusion, args, pool, witnesses, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_args(args, 8..)?;
    assert_clause_len(conclusion, 1)?;
    let (p, l, r, lo, hi) = (&args[0], &args[1], &args[2], &args[3], &args[4]);
    let (sturm, rest) = take_counted_pairs(&args[5..])?;
    let (sturm_tarski_l, rest) = take_counted_pairs(rest)?;
    let (sturm_tarski_r, rest) = take_counted_pairs(rest)?;
    rassert!(
        rest.is_empty(),
        CheckerError::WrongNumberOfArgs((args.len() - rest.len()).into(), args.len()),
    );

    let (conclusion_p, conclusion_l, conclusion_r) =
        match_term_err!((sgn_inv p l r) = &conclusion[0])?;
    assert_eq(conclusion_p, p)?;
    assert_eq(conclusion_l, l)?;
    assert_eq(conclusion_r, r)?;

    let var = poly_variable(pool, p)?;
    let p_coeffs = term_to_upoly(p, &var)?;
    rassert!(
        !p_coeffs.is_empty(),
        CoveringsError::ZeroPolynomial(p.clone())
    );
    rassert!(
        !is_plus_inf(l) && !is_minus_inf(r),
        CoveringsError::InvalidInterval(l.clone(), r.clone()),
    );

    // The finite endpoints are roots of `p`; this also validates the witnesses
    let mut finite_endpoints = 0;
    for (endpoint, sequence) in [(l, &sturm_tarski_l), (r, &sturm_tarski_r)] {
        if is_infinite(endpoint) {
            rassert!(
                sequence.is_empty(),
                CoveringsError::UnexpectedSequence(endpoint.clone()),
            );
        } else {
            check_root(witnesses, p, &p_coeffs, endpoint, sequence, &var)?;
            finite_endpoints += 1;
        }
    }
    rassert!(
        endpoint_lt(witnesses, l, r)?,
        CoveringsError::InvalidInterval(l.clone(), r.clone()),
    );
    let lo_value = check_window_bound(witnesses, &p_coeffs, l, lo, true)?;
    let hi_value = check_window_bound(witnesses, &p_coeffs, r, hi, false)?;

    // `p` has no roots in the window other than the endpoints
    let seq = terms_to_sequence(&sturm, &var)?;
    check_sturm_sequence(&seq, &p_coeffs)?;
    let variations = |bound: &Option<Rational>, positive: bool| match bound {
        Some(value) => sign_variations_at(&seq, value),
        None => sign_variations_at_inf(&seq, positive),
    };
    let roots = variations(&lo_value, false) - variations(&hi_value, true);
    rassert!(
        roots == finite_endpoints,
        CoveringsError::UnexpectedRoots(roots, finite_endpoints),
    );
    Ok(())
}

/// The `is_root_intro` rule: concludes `(@is_root p r)`, that is, that `r` is a root of the
/// polynomial `p`, from the arguments `p r` followed by the Sturm-Tarski sequence of `(q, q' * p)`
/// for a witness `r` with defining polynomial `q`, as a flattened sequence of pairs (see
/// `check_root`).
pub fn is_root_intro(
    RuleArgs {
        conclusion, args, pool, witnesses, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_args(args, 2..)?;
    assert_clause_len(conclusion, 1)?;
    let (p, r) = (&args[0], &args[1]);
    let sequence = as_pairs(&args[2..])?;

    let (conclusion_p, conclusion_r) = match_term_err!((is_root p r) = &conclusion[0])?;
    assert_eq(conclusion_p, p)?;
    assert_eq(conclusion_r, r)?;

    let var = poly_variable(pool, p)?;
    let p_coeffs = term_to_upoly(p, &var)?;
    rassert!(
        !p_coeffs.is_empty(),
        CoveringsError::ZeroPolynomial(p.clone())
    );
    check_root(witnesses, p, &p_coeffs, r, &sequence, &var)?;
    Ok(())
}

/// The `sgn_inv_elim` rule: from the premises `(@sgn_inv p l r)`, stating that `p` has a constant
/// sign on the open interval `(l, r)`, and a literal `(~ p 0)` or `(not (~ p 0))`, and given the
/// arguments `x p s l r` with `s` a rational in the interval at which the literal is false,
/// concludes that `x` is not in the interval: `(not (and (> x l) (< x r)))`, without the conjunct
/// of an infinite endpoint, or `false` if the interval is the whole line.
pub fn sgn_inv_elim(
    RuleArgs {
        conclusion,
        premises,
        args,
        pool,
        witnesses,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_num_args(args, 5)?;
    assert_clause_len(conclusion, 1)?;
    let (x, p, s, l, r) = (&args[0], &args[1], &args[2], &args[3], &args[4]);
    expect_variable(x)?;

    let (inv_p, inv_l, inv_r) =
        match_term_err!((sgn_inv inv_p inv_l inv_r) = get_premise_term(&premises[0])?)?;
    assert_eq(inv_p, p)?;
    assert_eq(inv_l, l)?;
    assert_eq(inv_r, r)?;

    let literal = get_premise_term(&premises[1])?;
    let (op, negated, literal_p) = as_literal(literal)?;
    assert_eq(literal_p, p)?;

    let sample = s
        .as_fraction()
        .ok_or_else(|| CheckerError::ExpectedAnyNumber(s.clone()))?;
    validate_endpoint(witnesses, l, x)?;
    validate_endpoint(witnesses, r, x)?;
    rassert!(
        endpoint_lt(witnesses, l, s)? && endpoint_lt(witnesses, s, r)?,
        CoveringsError::SampleNotInInterval(s.clone(), l.clone(), r.clone()),
    );
    let value = eval_at(p, x, &sample)?;
    rassert!(
        !literal_holds(op, negated, &value),
        CoveringsError::LiteralNotFalseAt(literal.clone(), value),
    );

    match open_piece(pool, x, l, r) {
        Some(piece) => assert_is_expected(&conclusion[0], build_term!(pool, (not { piece }))),
        None => assert_is_bool_constant(&conclusion[0], false),
    }
}

/// The `ran_eval` rule: from the premises `(@is_root p r)` and a literal `(~ p 0)` or
/// `(not (~ p 0))` that is false when `p` is zero, and given the arguments `x r p`, concludes
/// `(not (= x r))`.
pub fn ran_eval(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_num_args(args, 3)?;
    assert_clause_len(conclusion, 1)?;
    let (x, r, p) = (&args[0], &args[1], &args[2]);
    expect_variable(x)?;

    let (root_p, root_r) =
        match_term_err!((is_root root_p root_r) = get_premise_term(&premises[0])?)?;
    assert_eq(root_p, p)?;
    assert_eq(root_r, r)?;

    let literal = get_premise_term(&premises[1])?;
    let (op, negated, literal_p) = as_literal(literal)?;
    assert_eq(literal_p, p)?;
    rassert!(
        !literal_holds(op, negated, &Rational::new()),
        CoveringsError::LiteralNotFalseAt(literal.clone(), Rational::new()),
    );

    let (conclusion_x, conclusion_r) = match_term_err!((not (= x r)) = &conclusion[0])?;
    assert_eq(conclusion_x, x)?;
    assert_eq(conclusion_r, r)?;
    Ok(())
}
