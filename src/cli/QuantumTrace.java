package cli;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;

public class QuantumTrace extends Trace {
    public QuantumTrace(List<Assignment> assignments) {
        super(assignments);
    }

    private String simplifyKetList(List<ket> ketListSameCoeff, int dim){
        String fin = "";
        StringBuilder res = new StringBuilder("");
        List<ket> helperList = new ArrayList<>(ketListSameCoeff);
        List<Integer> bitpositions = new ArrayList<>();
        List<Integer> newnumbers = new ArrayList<>();

        for(int i = 0; i < ketListSameCoeff.size() - 1; i = i + 2){
            int checkInt = (ketListSameCoeff.get(i).bitIndex^ketListSameCoeff.get(i+1).bitIndex);
            if( checkInt != 0 && (checkInt & (checkInt-1))==0){
                helperList.remove(ketListSameCoeff.get(i));
                helperList.remove(ketListSameCoeff.get(i + 1));
                //exactly one bit is set => the numbers differ by only one bit
                int c;
                int bitposition = 0;
                while (checkInt != 0)
                {
                    c = checkInt & (0 - checkInt);
                    bitposition = Integer.numberOfTrailingZeros(c);
                    checkInt = checkInt ^ c;
                }
                //add position of bit change, and change bit to zero
                bitpositions.add(bitposition);

                int newnumber = ketListSameCoeff.get(i).bitIndex & ~(1 << bitposition);
                newnumbers.add(newnumber);

                res = new StringBuilder("|" + String.format("%" + dim + "s", Integer.toBinaryString(ketListSameCoeff.get(i).bitIndex)).replace(' ', '0') + ">");
                res.setCharAt( res.length() - bitposition - 2, 'x');

            }else{
                //return unprocessed term
                for(int j = 0; j < helperList.size(); j++){
                    if (j == 0 && res.length() == 0) {
                        fin += "|" + String.format("%" + dim + "s", Integer.toBinaryString(helperList.get(j).bitIndex)).replace(' ', '0') + ">";
                        continue;
                    }
                    fin += " + " + "|" + String.format("%" + dim + "s", Integer.toBinaryString(helperList.get(j).bitIndex)).replace(' ', '0') + ">";

                }
                break;
            }

            if(fin == ""){
                fin += res.toString();
            }else{
                fin += " + ";
                fin += res.toString();
            }
        }


        if(bitpositions.size() >= 2){
            for(int i = 0; i < bitpositions.size() - 1; i = i + 2){
                if(bitpositions.get(0) == bitpositions.get(1)){
                    res = new StringBuilder("|" + String.format("%" + dim + "s", Integer.toBinaryString(newnumbers.get(i))).replace(' ', '0') + ">");

                    int checkInt = (newnumbers.get(i)^newnumbers.get(i+1));
                    if( checkInt != 0 && (checkInt & (checkInt-1))==0){
                        //exactly one bit is set => the numbers differ by only one bit
                        int c;
                        int bitposition = 0;
                        while (checkInt != 0)
                        {
                            c = checkInt & (0 - checkInt);
                            bitposition = Integer.numberOfTrailingZeros(c);
                            checkInt = checkInt ^ c;
                        }
                        res.setCharAt( res.length() - bitposition - 2, 'x');
                    }

                    res.setCharAt( res.length() - bitpositions.get(i) - 2, 'x');

                }
                fin = res.toString();
            }

        }

        return fin;
    }

    private String simplifyQstate(List<ket> ketList, int dim){

        List<ket> ketListSameCoeff = new ArrayList<>();
        List<List<ket>> ketketList = new ArrayList<>();
        float currentCoeff = 0.0f;

        for(int i = 0; i < ketList.size(); i ++){
            currentCoeff = ketList.get(i).coeff;
            ketListSameCoeff.add(ketList.get(i));
            for(int j = i + 1; j < ketList.size(); j++){
                if(ketList.get(j).coeff == currentCoeff){
                    ketListSameCoeff.add(ketList.get(j));
                    ketList.remove(ketList.get(j));
                    j = j - 1;
                }
            }
            ketketList.add((List<ket>) ((ArrayList<ket>) ketListSameCoeff).clone());
            ketListSameCoeff.clear();
        }

        String valval = "";


        for(int i = 0; i < ketketList.size(); i++){
            if(i != 0){
                valval += " + ";
            }
            if(ketketList.get(i).size() > 1){
                valval += Float.toString(ketketList.get(i).get(0).coeff) + " * (";
                valval += simplifyKetList(ketketList.get(i), dim);
                valval += ")";
            }else{
                for (int j = 0; j < ketketList.get(i).size(); j++) {
                    valval += Float.toString(ketketList.get(i).get(0).coeff) + " * ";
                    valval += "|" + String.format("%" + dim + "s", Integer.toBinaryString(ketketList.get(i).get(j).bitIndex)).replace(' ', '0') + ">";

                }
            }
        }

        boolean printNormalVersion = false;
        if (printNormalVersion) {
            valval += "________";

            for (int j = 0; j < ketketList.size(); j++) {
                if (j != 0) {
                    valval += " + ";
                }
                String val = Float.toString(ketketList.get(j).get(0).coeff) + " * (";
                for (int i = 0; i < ketketList.get(j).size(); i++) {

                    if (i == 0) {
                        val += "|" + String.format("%" + dim + "s", Integer.toBinaryString(ketketList.get(j).get(i).bitIndex)).replace(' ', '0') + ">";
                        continue;
                    }
                    val += " + " + "|" + String.format("%" + dim + "s", Integer.toBinaryString(ketketList.get(j).get(i).bitIndex)).replace(' ', '0') + ">";
                }

                val += ")";
                valval += val;
            }

        }

        return valval;
    }

    private void createQuantumAss(Assignment qstate){
        List<Float> qvalues = new ArrayList<>();
        if(qstate.guessedValue == null) {
            return;
        } else {
            if(!(qstate.guessedValue instanceof ArrayList)) {
                return;
            }
            List<Object> values = (ArrayList<Object>)qstate.guessedValue;
            for(Object val : values) {
                if(val instanceof Float) {
                    qvalues.add((Float)val);
                } else if(val instanceof String) {
                    String sval = (String)val;
                    sval = sval.substring(sval.indexOf("/*") + 2, sval.indexOf("*/"));
                    sval = sval.trim();
                    qvalues.add(Float.parseFloat(sval));
                } else {
                    throw new RuntimeException("Error parsing qstate.");
                }
            }

        }
        int dim = qvalues.size();

        List<ket> ketList = new ArrayList<>();

        String val = "";
        for(int i = 0; i < qvalues.size(); i++){
            if(qvalues.get(i) > 0.0f || qvalues.get(i) < 0.0f){
                float coeff = qvalues.get(i);
                val += " + " + Float.toString(coeff) + " * " + "|" + String.format("%" + dim + "s", Integer.toBinaryString(i)).replace(' ', '0') + ">";

                ket k = new ket();
                k.coeff = coeff;
                k.bitIndex = i;
                ketList.add(k);
            }
        }

        String simplifiedVal = simplifyQstate(ketList, dim);
        val = val.substring(1);

        qstate.guessedValue = simplifiedVal;
    }
    @Override
    protected List<Assignment> filterGroup(List<Assignment> group) {
        //group = group.stream().filter(a -> !a.value.contains("dynamic_object")).collect(Collectors.toList());
        LinkedHashMap<String, Assignment> groupMap = new LinkedHashMap<>();

        for (Assignment a : group) {
            groupMap.put(a.guess, a);
        }
        List<Assignment> filtered = new ArrayList<>(groupMap.values());

        for (Assignment a : filtered) {
            if(a.guess != null) {
                if (a.guess.startsWith("q_state_0")) {
                    createQuantumAss(a);
                }
            }
        }

        return filtered;
    }
}
