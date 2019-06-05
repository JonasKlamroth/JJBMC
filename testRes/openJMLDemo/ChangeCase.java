//package openjml.demo;

public class ChangeCase {

    //Two times > instead of >= used to correct error.


    //@   requires c >= 'a' && c <= 'z';
    //@   ensures \result >= 'A' && \result <= 'Z';
    public char changeCase(char c) {
        char result = ' ';
        if (c > 'z') {
            result = c;
        } else if (c >= 'a') {
            result =  (char)(c - 'a' + 'A');
        } else if (c > 'Z') {
            result =  c;
        } else if (c >= 'A') {
            result =  (char)(c - 'A' + 'a');
        } else {
            result = c;
        }
        return result;
    }

    //@   requires c >= 'A' && c <= 'Z';
    //@   ensures \result >= 'a' && \result <= 'z';
    public char changeCase1(char c) {
        char result = ' ';
        if (c > 'z') {
            result = c;
        } else if (c >= 'a') {
            result =  (char)(c - 'a' + 'A');
        } else if (c > 'Z') {
            result =  c;
        } else if (c >= 'A') {
            result =  (char)(c - 'A' + 'a');
        } else {
            result = c;
        }
        return result;
    }

    //@   requires !(c >= 'A' && c <= 'Z') && !(c >= 'a' && c <= 'z');
    //@   ensures \result == c;
    public char changeCase2(char c) {
        char result = ' ';
        if (c > 'z') {
            result = c;
        } else if (c >= 'a') {
            result =  (char)(c - 'a' + 'A');
        } else if (c > 'Z') {
            result =  c;
        } else if (c >= 'A') {
            result =  (char)(c - 'A' + 'a');
        } else {
            result = c;
        }
        return result;
    }

}