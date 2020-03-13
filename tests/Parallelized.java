import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.runners.Parameterized;
import org.junit.runners.model.RunnerScheduler;

import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class Parallelized extends Parameterized
{
    private static class ThreadPoolScheduler implements RunnerScheduler
    {
        private ExecutorService executor;

        public ThreadPoolScheduler(int numThreads)
        {
            executor = Executors.newFixedThreadPool(numThreads);
            log.info("Parallelize test with " + numThreads + " threads.");
        }

        public ThreadPoolScheduler()
        {
            String threads = System.getProperty("junit.parallel.threads", "8");
            int numThreads = Integer.parseInt(threads);
            executor = Executors.newFixedThreadPool(numThreads);
            log.info("Parallelize test with " + numThreads + " threads.");
        }

        @Override
        public void finished()
        {
            executor.shutdown();
            try
            {
                executor.awaitTermination(10, TimeUnit.MINUTES);
            }
            catch (InterruptedException exc)
            {
                throw new RuntimeException(exc);
            }
        }

        @Override
        public void schedule(Runnable childStatement)
        {
            executor.submit(childStatement);
        }
    }

    private static Logger log = LogManager.getLogger(Parallelized.class);

    public Parallelized(Class klass) throws Throwable
    {
        super(klass);
        ThreadPoolScheduler tps = null;
        try {
            Field fThreads = klass.getField("numThreads");
            if(java.lang.reflect.Modifier.isStatic(fThreads.getModifiers()) && java.lang.reflect.Modifier.isFinal(fThreads.getModifiers())) {
                int numThreads = fThreads.getInt(null);
                tps = new ThreadPoolScheduler(numThreads);
            } else {
                log.warn("numThreads variable has to be static and final. Using default value.");
                tps = new ThreadPoolScheduler();
            }
        } catch (NoSuchFieldException e) {
            tps = new ThreadPoolScheduler();
        }

        setScheduler(tps);
    }
}