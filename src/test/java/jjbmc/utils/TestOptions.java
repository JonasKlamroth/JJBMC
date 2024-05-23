package jjbmc.utils;

import jjbmc.FunctionNameVisitor;

public record TestOptions(FunctionNameVisitor.TestBehaviour behaviour, int unwinds, String functionName) {
}
