# External LLM Prompt Logs

Use timestamped filenames for same-day ordering:

```text
YYYYMMDD-HHMMSS-<service>-short-topic.md
```

`<service>` identifies the source (e.g., `chatgpt`, `codex`). The timestamp
should be local time at which the response was saved or imported. This keeps
directory listings and GitHub views in chronological order even when several
responses arrive on the same day.
