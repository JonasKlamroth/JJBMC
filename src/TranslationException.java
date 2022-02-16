public class TranslationException extends RuntimeException {
    String message = "";

    public TranslationException(String message) {
        this.message = message;
    }
    @Override
    public String getMessage() {
        return "Unexpected behavior during translation. Please contact the developers: " + message;
    }

    public String getInnerMessage() {
        return message;
    }
}
