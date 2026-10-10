use super::ParserError;
use rug::Rational;

/// Parses a libpoly monomial, into its coefficient and degree.
fn parse_monom(s: &str) -> Result<(Rational, usize), ParserError> {
    let err = || ParserError::InvalidRealAlgebraicNumber(s.to_owned());
    // Monomials with a negative coefficient are wrapped in parentheses, e.g. `(-3*x^2)`
    let monom = s
        .strip_prefix('(')
        .and_then(|m| m.strip_suffix(')'))
        .unwrap_or(s);
    let (coeff, deg) = if let Some((coeff, pp)) = monom.split_once('*') {
        let deg = if let Some((_, rest)) = pp.split_once('^') {
            rest.parse::<usize>().map_err(|_| err())?
        } else {
            1
        };
        (coeff, deg)
    } else {
        (monom, 0)
    };
    Ok((coeff.parse::<Rational>().map_err(|_| err())?, deg))
}

/// Parses a real algebraic number in libpoly output format, without the enclosing `<` and `>`.
/// Returns the coefficients of the defining polynomial, from the lowest to the highest degree,
/// and the lower and upper bounds of the isolating interval.
pub fn parse_ran(s: &str) -> Result<(Vec<Rational>, Rational, Rational), ParserError> {
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

    Ok((coeffs, lower, upper))
}
