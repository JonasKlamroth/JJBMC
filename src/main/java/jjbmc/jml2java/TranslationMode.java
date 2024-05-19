package jjbmc.jml2java;

public enum TranslationMode {
    ASSUME,
    ASSERT,
    JAVA,
    DEMONIC;

    public TranslationMode switchPolarity() {
        return switch (this) {
            case ASSERT -> ASSUME;
            case ASSUME -> ASSERT;
            default -> this;
        };
    }
}