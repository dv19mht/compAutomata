/*
 * FFLOAT  Copyright (C) 2015  Riccardo De Masellis.
 *
 * This program comes with ABSOLUTELY NO WARRANTY.
 * This is free software, and you are welcome to redistribute it
 * under certain conditions; see http://www.gnu.org/licenses/gpl-3.0.html for details.
 */

package formula.regExp;

import formula.BinaryFormula;
import formula.Formula;
import symbols.Symbol;

/**
 * Created by Riccardo De Masellis on 21/05/15.
 * For any issue please write to r.demasellis@trentorise.eu.
 */
public abstract class RegExpBinary<S extends Symbol<?>> implements RegExp<S>, BinaryFormula<S> {
    private RegExp<S> left, right;

    public RegExpBinary(RegExp<S> left, RegExp<S> right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        RegExpBinary<?> that = (RegExpBinary<?>) o;

        if (left != null ? !left.equals(that.left) : that.left != null) return false;
        return !(right != null ? !right.equals(that.right) : that.right != null);

    }

    @Override
    public int hashCode() {
        int result = left != null ? left.hashCode() : 0;
        result = 31 * result + (right != null ? right.hashCode() : 0);
        return result;
    }

    public RegExp<S> getLeftFormula() {
        return left;
    }

    public RegExp<S> getRightFormula() {
        return right;
    }

    public String toString() {
        return "(" + this.getLeftFormula() + ") " + this.stringOperator() + " (" + this.getRightFormula() + ")";
    }

    @Override
    public RegExpBinary<S> clone() {
        return (RegExpBinary<S>) this.formulaFactory(this.getFormulaType(), (Formula<S>) this.getLeftFormula().clone(), (Formula<S>) this.getRightFormula().clone(), null);
    }
}
