/*
 * FFLOAT  Copyright (C) 2015  Riccardo De Masellis.
 *
 * This program comes with ABSOLUTELY NO WARRANTY.
 * This is free software, and you are welcome to redistribute it
 * under certain conditions; see http://www.gnu.org/licenses/gpl-3.0.html for details.
 */

package formula.ltlf;

import formula.FormulaType;
import formula.ldlf.LDLfFormula;

/**
 * Created by Riccardo De Masellis on 15/05/15.
 * For any issue please write to r.demasellis@trentorise.eu.
 */
public class LTLfWeakUntilFormula extends LTLfBinaryFormula implements LTLfTempOpTempFormula {

    public LTLfWeakUntilFormula(LTLfFormula left, LTLfFormula right) {
        super(left, right);
    }

    @Override
    public String stringOperator() {
        return "WU";
    }

    // Wikipedia: phi WU psi = psi R (psi OR phi)
    @Override
    public LTLfFormula nnf() {
        LTLfFormula left = (LTLfFormula) this.getLeftFormula().nnf();
        LTLfFormula right = (LTLfFormula) this.getRightFormula().nnf();
        LTLfFormula or;

        if (left instanceof LTLfLocalFormula && right instanceof LTLfLocalFormula)
            or = new LTLfLocalOrFormula(left, right);

        else
            or = new LTLfTempOrFormula(left, right);

        return new LTLfReleaseFormula(left, or);
    }

    @Override
    public LTLfFormula negate() {
        return (LTLfFormula) this.nnf().negate();
    }

    @Override
    public FormulaType getFormulaType() {
        return FormulaType.LTLf_WEAK_UNTIL;
    }


    @Override
    public LDLfFormula toLDLf() {
        return this.nnf().toLDLf();
    }
}