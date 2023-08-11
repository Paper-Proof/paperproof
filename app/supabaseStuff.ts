import { createClient } from "@supabase/supabase-js";
// Creating a new paperproof working session
supabase
  .from("sessions")
  .insert([{ proof: {} }])
  .select()
  .then(({ data, error }) => {
    if (error) {
      log.appendLine(
        `❌ Error in creating a new session: "${error.message}"`
      );
      return;
    }
    const id = data[0].id;
    log.appendLine(`🎉 New session: ${id}`);
    sessionId = id;
    if (latestInfo) {
      sendTypesToServer(id, latestInfo).then(() => {
        log.appendLine("🎉 Pending types sent");
      });
    }

    context.subscriptions.push(setupStatusBar(SERVER_URL, id));
  });




const supabaseUrl = "https://rksnswkaoajpdomeblni.supabase.co";
const supabaseKey =
  "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InJrc25zd2thb2FqcGRvbWVibG5pIiwicm9sZSI6ImFub24iLCJpYXQiOjE2OTAwNjU2NjgsImV4cCI6MjAwNTY0MTY2OH0.gmF1yF-iBhzlUgalz1vT28Jbc-QoOr5OlgI2MQ5OXhg";
const supabase = createClient(supabaseUrl, supabaseKey);



const sendTypesToServer = async (
  sessionId: string,
  body: ProofState | ProofError
) =>
  await supabase
    .from("sessions")
    .update([{ proof: body }])
    .eq("id", sessionId);
