use super::ParserError;
use crate::ast::RealAlgebraicNumber;
use rug::Rational;

/// Parses a libpoly monomial, into its coefficient and degree.
fn parse_monom(s: &str) -> Result<(Rational, usize), ParserError> {
    let err = || ParserError::InvalidRealAlgebraicNumber(s.to_owned());
    let (coeff, deg) = if let Some((coeff, pp)) = s.split_once('*') {
        let deg = if let Some((_, rest)) = pp.split_once('^') {
            rest.parse::<usize>().map_err(|_| err())?
        } else {
            1
        };
        (coeff, deg)
    } else {
        (s, 0)
    };
    // Negative coefficients are wrapped in parentheses, e.g. `(-2)`
    let coeff = coeff
        .strip_prefix('(')
        .and_then(|c| c.strip_suffix(')'))
        .unwrap_or(coeff);
    Ok((coeff.parse::<Rational>().map_err(|_| err())?, deg))
}

/// Parses a real algebraic number in libpoly output format, without the enclosing `<` and `>`.
/// The coefficients of the polynomial are stored from the
/// lowest to the highest degree.
pub fn parse_ran(s: &str) -> Result<RealAlgebraicNumber, ParserError> {
    let err = || ParserError::InvalidRealAlgebraicNumber(s.to_owned());
    let (poly, interval) = s.split_once(", ").ok_or_else(err)?;
    // The interval is `(a, b)`, with `[`/`]` for closed ends, or `[a]` for a point
    let bounds = interval
        .strip_prefix(['(', '['])
        .and_then(|i| i.strip_suffix([')', ']']))
        .ok_or_else(err)?;
    let parse_bound = |b: &str| b.parse::<Rational>().map_err(|_| err());
    let (lower, upper) = match bounds.split_once(", ") {
        Some((lower, upper)) => (parse_bound(lower)?, parse_bound(upper)?),
        None => {
            let point = parse_bound(bounds)?;
            (point.clone(), point)
        }
    };

    let monoms = poly
        .split(" + ")
        .map(parse_monom)
        .collect::<Result<Vec<_>, _>>()?;
    let degree = monoms.first().map_or(0, |(_, deg)| *deg);
    let mut coeffs = vec![Rational::new(); degree + 1];
    let mut prev_deg = None;
    for (coeff, deg) in monoms {
        if prev_deg.is_some_and(|prev| deg >= prev) {
            return Err(err());
        }
        coeffs[deg] = coeff;
        prev_deg = Some(deg);
    }

    Ok(RealAlgebraicNumber { poly: coeffs, lower, upper })
}
