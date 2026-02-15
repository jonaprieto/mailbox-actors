#!/bin/bash
echo "Checking for axioms and sorrys..."
grep -r "axiom" formalization/MailboxActors/MailboxActors/Properties
grep -r "sorry" formalization/MailboxActors/MailboxActors/Properties
grep -r "constant" formalization/MailboxActors/MailboxActors/Properties
echo "Done."

