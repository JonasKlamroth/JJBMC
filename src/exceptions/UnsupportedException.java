package exceptions;

public class UnsupportedException extends RuntimeException {
    String message = "";

    public UnsupportedException(String message) {
        this.message = message;
    }

    @Override
    public String getMessage() {
        return "Encountered unsupported syntax: " + message;
    }

    public String getInnerMessage() {
        return message;
    }
}
