import V185TrunkScan22Chunk450

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4020932 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4020932 : Nat := 118140960795 + 4020932 * 2 ^ 59
def prefixEnd_4020932 : Nat := 4983230072969 + 3 ^ 40 * 4020932 * 2
def baseEnd_4020932 : Nat := 1376447196696244879172051

theorem tailTrace_4020932 : CollatzResearch.WordTrace tailWord_4020932 prefixEnd_4020932 1376447196696244879172051 := by
  unfold tailWord_4020932
  simp only [CollatzResearch.WordTrace]
  refine ⟨73327719134428779679048525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97770292179238372905398033 73327719134428779679048525)
  ·
    refine ⟨27497894675410792379643197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73327719134428779679048525 27497894675410792379643197)
    ·
      refine ⟨10311710503279047142366199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27497894675410792379643197 10311710503279047142366199)
      ·
        refine ⟨15467565754918570713549299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311710503279047142366199 15467565754918570713549299)
        ·
          refine ⟨23201348632377856070323949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15467565754918570713549299 23201348632377856070323949)
          ·
            refine ⟨8700505737141696026371481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23201348632377856070323949 8700505737141696026371481)
            ·
              refine ⟨6525379302856272019778611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700505737141696026371481 6525379302856272019778611)
              ·
                refine ⟨9788068954284408029667917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525379302856272019778611 9788068954284408029667917)
                ·
                  refine ⟨3670525857856653011125469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9788068954284408029667917 3670525857856653011125469)
                  ·
                    refine ⟨1376447196696244879172051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670525857856653011125469 1376447196696244879172051)
                    ·
                      rfl

theorem cell22_4020932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4020932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020932 prefixEnd_4020932 := by exact prefixLift 4020932
  have htrace : WordTrace (prefixWord ++ tailWord_4020932) baseStart_4020932 baseEnd_4020932 := by
    simpa [prefixWord, tailWord_4020932, baseEnd_4020932] using wordTrace_append hprefix tailTrace_4020932
  have hstable : (prefixWord ++ tailWord_4020932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020932).length < 2 ^ (prefixWord ++ tailWord_4020932).sum := by decide
  have hdescent : baseEnd_4020932 < baseStart_4020932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020945 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 5]
def baseStart_4020945 : Nat := 118140960795 + 4020945 * 2 ^ 59
def prefixEnd_4020945 : Nat := 4983230072969 + 3 ^ 40 * 4020945 * 2
def baseEnd_4020945 : Nat := 458817215620639059532337

theorem tailTrace_4020945 : CollatzResearch.WordTrace tailWord_4020945 prefixEnd_4020945 458817215620639059532337 := by
  unfold tailWord_4020945
  simp only [CollatzResearch.WordTrace]
  refine ⟨146655912417810462578320289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97770608278540308385546859 146655912417810462578320289)
  ·
    refine ⟨109991934313357846933740217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146655912417810462578320289 109991934313357846933740217)
    ·
      refine ⟨82493950735018385200305163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109991934313357846933740217 82493950735018385200305163)
      ·
        refine ⟨123740926102527577800457745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82493950735018385200305163 123740926102527577800457745)
        ·
          refine ⟨92805694576895683350343309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123740926102527577800457745 92805694576895683350343309)
          ·
            refine ⟨34802135466335881256378741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92805694576895683350343309 34802135466335881256378741)
            ·
              refine ⟨3262700199968988867785507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34802135466335881256378741 3262700199968988867785507)
              ·
                refine ⟨4894050299953483301678261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262700199968988867785507 4894050299953483301678261)
                ·
                  refine ⟨458817215620639059532337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4894050299953483301678261 458817215620639059532337)
                  ·
                    rfl

theorem cell22_4020945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_4020945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020945 prefixEnd_4020945 := by exact prefixLift 4020945
  have htrace : WordTrace (prefixWord ++ tailWord_4020945) baseStart_4020945 baseEnd_4020945 := by
    simpa [prefixWord, tailWord_4020945, baseEnd_4020945] using wordTrace_append hprefix tailTrace_4020945
  have hstable : (prefixWord ++ tailWord_4020945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020945).length < 2 ^ (prefixWord ++ tailWord_4020945).sum := by decide
  have hdescent : baseEnd_4020945 < baseStart_4020945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020975 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 1, 4]
def baseStart_4020975 : Nat := 118140960795 + 4020975 * 2 ^ 59
def prefixEnd_4020975 : Nat := 4983230072969 + 3 ^ 40 * 4020975 * 2
def baseEnd_4020975 : Nat := 1376461916475007100346919

theorem tailTrace_4020975 : CollatzResearch.WordTrace tailWord_4020975 prefixEnd_4020975 1376461916475007100346919 := by
  unfold tailWord_4020975
  simp only [CollatzResearch.WordTrace]
  refine ⟨146657006607701777701912379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97771337738467851801274919 146657006607701777701912379)
  ·
    refine ⟨219985509911552666552868569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146657006607701777701912379 219985509911552666552868569)
    ·
      refine ⟨164989132433664499914651427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219985509911552666552868569 164989132433664499914651427)
      ·
        refine ⟨247483698650496749871977141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164989132433664499914651427 247483698650496749871977141)
        ·
          refine ⟨23201596748484070300497857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247483698650496749871977141 23201596748484070300497857)
          ·
            refine ⟨17401197561363052725373393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23201596748484070300497857 17401197561363052725373393)
            ·
              refine ⟨13050898171022289544030045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17401197561363052725373393 13050898171022289544030045)
              ·
                refine ⟨4894086814133358579011267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13050898171022289544030045 4894086814133358579011267)
                ·
                  refine ⟨7341130221200037868516901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894086814133358579011267 7341130221200037868516901)
                  ·
                    refine ⟨1376461916475007100346919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341130221200037868516901 1376461916475007100346919)
                    ·
                      rfl

theorem cell22_4020975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_4020975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020975 prefixEnd_4020975 := by exact prefixLift 4020975
  have htrace : WordTrace (prefixWord ++ tailWord_4020975) baseStart_4020975 baseEnd_4020975 := by
    simpa [prefixWord, tailWord_4020975, baseEnd_4020975] using wordTrace_append hprefix tailTrace_4020975
  have hstable : (prefixWord ++ tailWord_4020975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020975).length < 2 ^ (prefixWord ++ tailWord_4020975).sum := by decide
  have hdescent : baseEnd_4020975 < baseStart_4020975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021003 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 6, 4]
def baseStart_4021003 : Nat := 118140960795 + 4021003 * 2 ^ 59
def prefixEnd_4021003 : Nat := 4983230072969 + 3 ^ 40 * 4021003 * 2
def baseEnd_4021003 : Nat := 1376471501447224360646833

theorem tailTrace_4021003 : CollatzResearch.WordTrace tailWord_4021003 prefixEnd_4021003 1376471501447224360646833 := by
  unfold tailWord_4021003
  simp only [CollatzResearch.WordTrace]
  refine ⟨146658027851600338483931663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97772018567733558989287775 146658027851600338483931663)
  ·
    refine ⟨219987041777400507725897495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146658027851600338483931663 219987041777400507725897495)
    ·
      refine ⟨329980562666100761588846243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219987041777400507725897495 329980562666100761588846243)
      ·
        refine ⟨494970843999151142383269365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329980562666100761588846243 494970843999151142383269365)
        ·
          refine ⟨46403516624920419598431503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 494970843999151142383269365 46403516624920419598431503)
          ·
            refine ⟨69605274937380629397647255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46403516624920419598431503 69605274937380629397647255)
            ·
              refine ⟨104407912406070944096470883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69605274937380629397647255 104407912406070944096470883)
              ·
                refine ⟨156611868609106416144706325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104407912406070944096470883 156611868609106416144706325)
                ·
                  refine ⟨7341181341051863256783109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156611868609106416144706325 7341181341051863256783109)
                  ·
                    refine ⟨1376471501447224360646833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341181341051863256783109 1376471501447224360646833)
                    ·
                      rfl

theorem cell22_4021003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_4021003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021003 prefixEnd_4021003 := by exact prefixLift 4021003
  have htrace : WordTrace (prefixWord ++ tailWord_4021003) baseStart_4021003 baseEnd_4021003 := by
    simpa [prefixWord, tailWord_4021003, baseEnd_4021003] using wordTrace_append hprefix tailTrace_4021003
  have hstable : (prefixWord ++ tailWord_4021003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021003).length < 2 ^ (prefixWord ++ tailWord_4021003).sum := by decide
  have hdescent : baseEnd_4021003 < baseStart_4021003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021018 : List Nat := [3, 1, 1, 3, 2, 1, 1, 10]
def baseStart_4021018 : Nat := 118140960795 + 4021018 * 2 ^ 59
def prefixEnd_4021018 : Nat := 4983230072969 + 3 ^ 40 * 4021018 * 2
def baseEnd_4021018 : Nat := 152941848472641035724643

theorem tailTrace_4021018 : CollatzResearch.WordTrace tailWord_4021018 prefixEnd_4021018 152941848472641035724643 := by
  unfold tailWord_4021018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36664643736636499011431927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97772383297697330697151805 36664643736636499011431927)
  ·
    refine ⟨54996965604954748517147891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36664643736636499011431927 54996965604954748517147891)
    ·
      refine ⟨82495448407432122775721837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54996965604954748517147891 82495448407432122775721837)
      ·
        refine ⟨30935793152787046040895689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82495448407432122775721837 30935793152787046040895689)
        ·
          refine ⟨23201844864590284530671767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30935793152787046040895689 23201844864590284530671767)
          ·
            refine ⟨34802767296885426796007651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23201844864590284530671767 34802767296885426796007651)
            ·
              refine ⟨52204150945328140194011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34802767296885426796007651 52204150945328140194011477)
              ·
                refine ⟨152941848472641035724643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52204150945328140194011477 152941848472641035724643)
                ·
                  rfl

theorem cell22_4021018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_4021018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021018 prefixEnd_4021018 := by exact prefixLift 4021018
  have htrace : WordTrace (prefixWord ++ tailWord_4021018) baseStart_4021018 baseEnd_4021018 := by
    simpa [prefixWord, tailWord_4021018, baseEnd_4021018] using wordTrace_append hprefix tailTrace_4021018
  have hstable : (prefixWord ++ tailWord_4021018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021018).length < 2 ^ (prefixWord ++ tailWord_4021018).sum := by decide
  have hdescent : baseEnd_4021018 < baseStart_4021018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021020 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_4021020 : Nat := 118140960795 + 4021020 * 2 ^ 59
def prefixEnd_4021020 : Nat := 4983230072969 + 3 ^ 40 * 4021020 * 2
def baseEnd_4021020 : Nat := 1376477320894641982971781

theorem tailTrace_4021020 : CollatzResearch.WordTrace tailWord_4021020 prefixEnd_4021020 1376477320894641982971781 := by
  unfold tailWord_4021020
  simp only [CollatzResearch.WordTrace]
  refine ⟨73329323946269375193650257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97772431928359166924867009 73329323946269375193650257)
  ·
    refine ⟨54996992959702031395237693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73329323946269375193650257 54996992959702031395237693)
    ·
      refine ⟨20623872359888261773214135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54996992959702031395237693 20623872359888261773214135)
      ·
        refine ⟨30935808539832392659821203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20623872359888261773214135 30935808539832392659821203)
        ·
          refine ⟨46403712809748588989731805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30935808539832392659821203 46403712809748588989731805)
          ·
            refine ⟨17401392303655720871149427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46403712809748588989731805 17401392303655720871149427)
            ·
              refine ⟨26102088455483581306724141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401392303655720871149427 26102088455483581306724141)
              ·
                refine ⟨9788283170806342990021553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26102088455483581306724141 9788283170806342990021553)
                ·
                  refine ⟨7341212378104757242516165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9788283170806342990021553 7341212378104757242516165)
                  ·
                    refine ⟨1376477320894641982971781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341212378104757242516165 1376477320894641982971781)
                    ·
                      rfl

theorem cell22_4021020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_4021020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021020 prefixEnd_4021020 := by exact prefixLift 4021020
  have htrace : WordTrace (prefixWord ++ tailWord_4021020) baseStart_4021020 baseEnd_4021020 := by
    simpa [prefixWord, tailWord_4021020, baseEnd_4021020] using wordTrace_append hprefix tailTrace_4021020
  have hstable : (prefixWord ++ tailWord_4021020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021020).length < 2 ^ (prefixWord ++ tailWord_4021020).sum := by decide
  have hdescent : baseEnd_4021020 < baseStart_4021020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021048 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_4021048 : Nat := 118140960795 + 4021048 * 2 ^ 59
def prefixEnd_4021048 : Nat := 4983230072969 + 3 ^ 40 * 4021048 * 2
def baseEnd_4021048 : Nat := 1376486905866859243271695

theorem tailTrace_4021048 : CollatzResearch.WordTrace tailWord_4021048 prefixEnd_4021048 1376486905866859243271695 := by
  unfold tailWord_4021048
  simp only [CollatzResearch.WordTrace]
  refine ⟨73329834568218655584659899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97773112757624874112879865 73329834568218655584659899)
  ·
    refine ⟨109994751852327983376989849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73329834568218655584659899 109994751852327983376989849)
    ·
      refine ⟨82496063889245987532742387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109994751852327983376989849 82496063889245987532742387)
      ·
        refine ⟨123744095833868981299113581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82496063889245987532742387 123744095833868981299113581)
        ·
          refine ⟨46404035937700867987167593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123744095833868981299113581 46404035937700867987167593)
          ·
            refine ⟨34803026953275650990375695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46404035937700867987167593 34803026953275650990375695)
            ·
              refine ⟨52204540429913476485563543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34803026953275650990375695 52204540429913476485563543)
              ·
                refine ⟨78306810644870214728345315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52204540429913476485563543 78306810644870214728345315)
                ·
                  refine ⟨117460215967305322092517973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78306810644870214728345315 117460215967305322092517973)
                  ·
                    refine ⟨1376486905866859243271695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117460215967305322092517973 1376486905866859243271695)
                    ·
                      rfl

theorem cell22_4021048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_4021048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021048 prefixEnd_4021048 := by exact prefixLift 4021048
  have htrace : WordTrace (prefixWord ++ tailWord_4021048) baseStart_4021048 baseEnd_4021048 := by
    simpa [prefixWord, tailWord_4021048, baseEnd_4021048] using wordTrace_append hprefix tailTrace_4021048
  have hstable : (prefixWord ++ tailWord_4021048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021048).length < 2 ^ (prefixWord ++ tailWord_4021048).sum := by decide
  have hdescent : baseEnd_4021048 < baseStart_4021048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021063 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 9]
def baseStart_4021063 : Nat := 118140960795 + 4021063 * 2 ^ 59
def prefixEnd_4021063 : Nat := 4983230072969 + 3 ^ 40 * 4021063 * 2
def baseEnd_4021063 : Nat := 458830680224468068048883

theorem tailTrace_4021063 : CollatzResearch.WordTrace tailWord_4021063 prefixEnd_4021063 458830680224468068048883 := by
  unfold tailWord_4021063
  simp only [CollatzResearch.WordTrace]
  refine ⟨146660216231382968731115843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97773477487588645820743895 146660216231382968731115843)
  ·
    refine ⟨219990324347074453096673765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146660216231382968731115843 219990324347074453096673765)
    ·
      refine ⟨41248185815076459955626331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219990324347074453096673765 41248185815076459955626331)
      ·
        refine ⟨61872278722614689933439497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41248185815076459955626331 61872278722614689933439497)
        ·
          refine ⟨46404209041961017450079623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61872278722614689933439497 46404209041961017450079623)
          ·
            refine ⟨69606313562941526175119435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46404209041961017450079623 69606313562941526175119435)
            ·
              refine ⟨104409470344412289262679153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69606313562941526175119435 104409470344412289262679153)
              ·
                refine ⟨78307102758309216947009365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104409470344412289262679153 78307102758309216947009365)
                ·
                  refine ⟨458830680224468068048883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78307102758309216947009365 458830680224468068048883)
                  ·
                    rfl

theorem cell22_4021063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_4021063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021063 prefixEnd_4021063 := by exact prefixLift 4021063
  have htrace : WordTrace (prefixWord ++ tailWord_4021063) baseStart_4021063 baseEnd_4021063 := by
    simpa [prefixWord, tailWord_4021063, baseEnd_4021063] using wordTrace_append hprefix tailTrace_4021063
  have hstable : (prefixWord ++ tailWord_4021063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021063).length < 2 ^ (prefixWord ++ tailWord_4021063).sum := by decide
  have hdescent : baseEnd_4021063 < baseStart_4021063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021069 : List Nat := [1, 6, 1, 2, 2, 1, 3, 6]
def baseStart_4021069 : Nat := 118140960795 + 4021069 * 2 ^ 59
def prefixEnd_4021069 : Nat := 4983230072969 + 3 ^ 40 * 4021069 * 2
def baseEnd_4021069 : Nat := 152943788288446909832959

theorem tailTrace_4021069 : CollatzResearch.WordTrace tailWord_4021069 prefixEnd_4021069 152943788288446909832959 := by
  unfold tailWord_4021069
  simp only [CollatzResearch.WordTrace]
  refine ⟨146660435069361231755834261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97773623379574154503889507 146660435069361231755834261)
  ·
    refine ⟨6874707893876307738554731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146660435069361231755834261 6874707893876307738554731)
    ·
      refine ⟨10312061840814461607832097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874707893876307738554731 10312061840814461607832097)
      ·
        refine ⟨7734046380610846205874073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10312061840814461607832097 7734046380610846205874073)
        ·
          refine ⟨5800534785458134654405555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7734046380610846205874073 5800534785458134654405555)
          ·
            refine ⟨8700802178187201981608333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800534785458134654405555 8700802178187201981608333)
            ·
              refine ⟨3262800816820200743103125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8700802178187201981608333 3262800816820200743103125)
              ·
                refine ⟨152943788288446909832959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3262800816820200743103125 152943788288446909832959)
                ·
                  rfl

theorem cell22_4021069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 6].length) (baseStart_4021069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021069 prefixEnd_4021069 := by exact prefixLift 4021069
  have htrace : WordTrace (prefixWord ++ tailWord_4021069) baseStart_4021069 baseEnd_4021069 := by
    simpa [prefixWord, tailWord_4021069, baseEnd_4021069] using wordTrace_append hprefix tailTrace_4021069
  have hstable : (prefixWord ++ tailWord_4021069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021069).length < 2 ^ (prefixWord ++ tailWord_4021069).sum := by decide
  have hdescent : baseEnd_4021069 < baseStart_4021069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021095 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4021095 : Nat := 118140960795 + 4021095 * 2 ^ 59
def prefixEnd_4021095 : Nat := 4983230072969 + 3 ^ 40 * 4021095 * 2
def baseEnd_4021095 : Nat := 1376502994927366787346551

theorem tailTrace_4021095 : CollatzResearch.WordTrace tailWord_4021095 prefixEnd_4021095 1376502994927366787346551 := by
  unfold tailWord_4021095
  simp only [CollatzResearch.WordTrace]
  refine ⟨146661383367267038196280739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97774255578178025464187159 146661383367267038196280739)
  ·
    refine ⟨219992075050900557294421109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146661383367267038196280739 219992075050900557294421109)
    ·
      refine ⟨20624257036021927246351979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219992075050900557294421109 20624257036021927246351979)
      ·
        refine ⟨30936385554032890869527969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20624257036021927246351979 30936385554032890869527969)
        ·
          refine ⟨23202289165524668152145977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30936385554032890869527969 23202289165524668152145977)
          ·
            refine ⟨17401716874143501114109483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23202289165524668152145977 17401716874143501114109483)
            ·
              refine ⟨26102575311215251671164225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401716874143501114109483 26102575311215251671164225)
              ·
                refine ⟨19576931483411438753373169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26102575311215251671164225 19576931483411438753373169)
                ·
                  refine ⟨14682698612558579065029877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19576931483411438753373169 14682698612558579065029877)
                  ·
                    refine ⟨1376502994927366787346551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14682698612558579065029877 1376502994927366787346551)
                    ·
                      rfl

theorem cell22_4021095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4021095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021095 prefixEnd_4021095 := by exact prefixLift 4021095
  have htrace : WordTrace (prefixWord ++ tailWord_4021095) baseStart_4021095 baseEnd_4021095 := by
    simpa [prefixWord, tailWord_4021095, baseEnd_4021095] using wordTrace_append hprefix tailTrace_4021095
  have hstable : (prefixWord ++ tailWord_4021095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021095).length < 2 ^ (prefixWord ++ tailWord_4021095).sum := by decide
  have hdescent : baseEnd_4021095 < baseStart_4021095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021125 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 6]
def baseStart_4021125 : Nat := 118140960795 + 4021125 * 2 ^ 59
def prefixEnd_4021125 : Nat := 4983230072969 + 3 ^ 40 * 4021125 * 2
def baseEnd_4021125 : Nat := 458837754846818903032153

theorem tailTrace_4021125 : CollatzResearch.WordTrace tailWord_4021125 prefixEnd_4021125 458837754846818903032153 := by
  unfold tailWord_4021125
  simp only [CollatzResearch.WordTrace]
  refine ⟨146662477557158353319872829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97774985038105568879915219 146662477557158353319872829)
  ·
    refine ⟨54998429083934382494952311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146662477557158353319872829 54998429083934382494952311)
    ·
      refine ⟨82497643625901573742428467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54998429083934382494952311 82497643625901573742428467)
      ·
        refine ⟨123746465438852360613642701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82497643625901573742428467 123746465438852360613642701)
        ·
          refine ⟨46404924539569635230116013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123746465438852360613642701 46404924539569635230116013)
          ·
            refine ⟨17401846702338613211293505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46404924539569635230116013 17401846702338613211293505)
            ·
              refine ⟨13051385026753959908470129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17401846702338613211293505 13051385026753959908470129)
              ·
                refine ⟨9788538770065469931352597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13051385026753959908470129 9788538770065469931352597)
                ·
                  refine ⟨458837754846818903032153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9788538770065469931352597 458837754846818903032153)
                  ·
                    rfl

theorem cell22_4021125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_4021125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021125 prefixEnd_4021125 := by exact prefixLift 4021125
  have htrace : WordTrace (prefixWord ++ tailWord_4021125) baseStart_4021125 baseEnd_4021125 := by
    simpa [prefixWord, tailWord_4021125, baseEnd_4021125] using wordTrace_append hprefix tailTrace_4021125
  have hstable : (prefixWord ++ tailWord_4021125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021125).length < 2 ^ (prefixWord ++ tailWord_4021125).sum := by decide
  have hdescent : baseEnd_4021125 < baseStart_4021125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021127 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 1, 4]
def baseStart_4021127 : Nat := 118140960795 + 4021127 * 2 ^ 59
def prefixEnd_4021127 : Nat := 4983230072969 + 3 ^ 40 * 4021127 * 2
def baseEnd_4021127 : Nat := 1376513949181329370546453

theorem tailTrace_4021127 : CollatzResearch.WordTrace tailWord_4021127 prefixEnd_4021127 1376513949181329370546453 := by
  unfold tailWord_4021127
  simp only [CollatzResearch.WordTrace]
  refine ⟨146662550503151107661445635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97775033668767405107630423 146662550503151107661445635)
  ·
    refine ⟨219993825754726661492168453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146662550503151107661445635 219993825754726661492168453)
    ·
      refine ⟨41248842329011249029781585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219993825754726661492168453 41248842329011249029781585)
      ·
        refine ⟨30936631746758436772336189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41248842329011249029781585 30936631746758436772336189)
        ·
          refine ⟨11601236905034413789626071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30936631746758436772336189 11601236905034413789626071)
          ·
            refine ⟨17401855357551620684439107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601236905034413789626071 17401855357551620684439107)
            ·
              refine ⟨26102783036327431026658661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401855357551620684439107 26102783036327431026658661)
              ·
                refine ⟨4894271819311393317498499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26102783036327431026658661 4894271819311393317498499)
                ·
                  refine ⟨7341407728967089976247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894271819311393317498499 7341407728967089976247749)
                  ·
                    refine ⟨1376513949181329370546453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341407728967089976247749 1376513949181329370546453)
                    ·
                      rfl

theorem cell22_4021127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_4021127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021127 prefixEnd_4021127 := by exact prefixLift 4021127
  have htrace : WordTrace (prefixWord ++ tailWord_4021127) baseStart_4021127 baseEnd_4021127 := by
    simpa [prefixWord, tailWord_4021127, baseEnd_4021127] using wordTrace_append hprefix tailTrace_4021127
  have hstable : (prefixWord ++ tailWord_4021127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021127).length < 2 ^ (prefixWord ++ tailWord_4021127).sum := by decide
  have hdescent : baseEnd_4021127 < baseStart_4021127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021155 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 4, 4]
def baseStart_4021155 : Nat := 118140960795 + 4021155 * 2 ^ 59
def prefixEnd_4021155 : Nat := 4983230072969 + 3 ^ 40 * 4021155 * 2
def baseEnd_4021155 : Nat := 1376523534153546630846367

theorem tailTrace_4021155 : CollatzResearch.WordTrace tailWord_4021155 prefixEnd_4021155 1376523534153546630846367 := by
  unfold tailWord_4021155
  simp only [CollatzResearch.WordTrace]
  refine ⟨146663571747049668443464919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97775714498033112295643279 146663571747049668443464919)
  ·
    refine ⟨219995357620574502665197379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146663571747049668443464919 219995357620574502665197379)
    ·
      refine ⟨329993036430861753997796069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219995357620574502665197379 329993036430861753997796069)
      ·
        refine ⟨61873694330786578874586763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329993036430861753997796069 61873694330786578874586763)
        ·
          refine ⟨92810541496179868311880145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61873694330786578874586763 92810541496179868311880145)
          ·
            refine ⟨69607906122134901233910109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92810541496179868311880145 69607906122134901233910109)
            ·
              refine ⟨26102964795800587962716291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69607906122134901233910109 26102964795800587962716291)
              ·
                refine ⟨39154447193700881944074437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26102964795800587962716291 39154447193700881944074437)
                ·
                  refine ⟨7341458848818915364513957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39154447193700881944074437 7341458848818915364513957)
                  ·
                    refine ⟨1376523534153546630846367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341458848818915364513957 1376523534153546630846367)
                    ·
                      rfl

theorem cell22_4021155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_4021155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021155 prefixEnd_4021155 := by exact prefixLift 4021155
  have htrace : WordTrace (prefixWord ++ tailWord_4021155) baseStart_4021155 baseEnd_4021155 := by
    simpa [prefixWord, tailWord_4021155, baseEnd_4021155] using wordTrace_append hprefix tailTrace_4021155
  have hstable : (prefixWord ++ tailWord_4021155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021155).length < 2 ^ (prefixWord ++ tailWord_4021155).sum := by decide
  have hdescent : baseEnd_4021155 < baseStart_4021155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021159 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 6]
def baseStart_4021159 : Nat := 118140960795 + 4021159 * 2 ^ 59
def prefixEnd_4021159 : Nat := 4983230072969 + 3 ^ 40 * 4021159 * 2
def baseEnd_4021159 : Nat := 458841634478430651248785

theorem tailTrace_4021159 : CollatzResearch.WordTrace tailWord_4021159 prefixEnd_4021159 458841634478430651248785 := by
  unfold tailWord_4021159
  simp only [CollatzResearch.WordTrace]
  refine ⟨146663717639035177126610531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97775811759356784751073687 146663717639035177126610531)
  ·
    refine ⟨219995576458552765689915797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146663717639035177126610531 219995576458552765689915797)
    ·
      refine ⟨10312292646494660891714803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219995576458552765689915797 10312292646494660891714803)
      ·
        refine ⟨15468438969741991337572205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10312292646494660891714803 15468438969741991337572205)
        ·
          refine ⟨5800664613653246751589577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15468438969741991337572205 5800664613653246751589577)
          ·
            refine ⟨4350498460239935063692183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800664613653246751589577 4350498460239935063692183)
            ·
              refine ⟨6525747690359902595538275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350498460239935063692183 6525747690359902595538275)
              ·
                refine ⟨9788621535539853893307413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525747690359902595538275 9788621535539853893307413)
                ·
                  refine ⟨458841634478430651248785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9788621535539853893307413 458841634478430651248785)
                  ·
                    rfl

theorem cell22_4021159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 6].length) (baseStart_4021159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021159 prefixEnd_4021159 := by exact prefixLift 4021159
  have htrace : WordTrace (prefixWord ++ tailWord_4021159) baseStart_4021159 baseEnd_4021159 := by
    simpa [prefixWord, tailWord_4021159, baseEnd_4021159] using wordTrace_append hprefix tailTrace_4021159
  have hstable : (prefixWord ++ tailWord_4021159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021159).length < 2 ^ (prefixWord ++ tailWord_4021159).sum := by decide
  have hdescent : baseEnd_4021159 < baseStart_4021159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021221 : List Nat := [1, 3, 1, 6, 2, 1, 1, 7]
def baseStart_4021221 : Nat := 118140960795 + 4021221 * 2 ^ 59
def prefixEnd_4021221 : Nat := 4983230072969 + 3 ^ 40 * 4021221 * 2
def baseEnd_4021221 : Nat := 152949569700260495410685

theorem tailTrace_4021221 : CollatzResearch.WordTrace tailWord_4021221 prefixEnd_4021221 152949569700260495410685 := by
  unfold tailWord_4021221
  simp only [CollatzResearch.WordTrace]
  refine ⟨146665978964810561715367517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97777319309873707810245011 146665978964810561715367517)
  ·
    refine ⟨54999742111803960643262819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146665978964810561715367517 54999742111803960643262819)
    ·
      refine ⟨82499613167705940964894229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54999742111803960643262819 82499613167705940964894229)
      ·
        refine ⟨3867169367236215982729417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82499613167705940964894229 3867169367236215982729417)
        ·
          refine ⟨2900377025427161987047063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867169367236215982729417 2900377025427161987047063)
          ·
            refine ⟨4350565538140742980570595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900377025427161987047063 4350565538140742980570595)
            ·
              refine ⟨6525848307211114470855893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350565538140742980570595 6525848307211114470855893)
              ·
                refine ⟨152949569700260495410685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6525848307211114470855893 152949569700260495410685)
                ·
                  rfl

theorem cell22_4021221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 7].length) (baseStart_4021221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021221 prefixEnd_4021221 := by exact prefixLift 4021221
  have htrace : WordTrace (prefixWord ++ tailWord_4021221) baseStart_4021221 baseEnd_4021221 := by
    simpa [prefixWord, tailWord_4021221, baseEnd_4021221] using wordTrace_append hprefix tailTrace_4021221
  have hstable : (prefixWord ++ tailWord_4021221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021221).length < 2 ^ (prefixWord ++ tailWord_4021221).sum := by decide
  have hdescent : baseEnd_4021221 < baseStart_4021221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021309 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_4021309 : Nat := 118140960795 + 4021309 * 2 ^ 59
def prefixEnd_4021309 : Nat := 4983230072969 + 3 ^ 40 * 4021309 * 2
def baseEnd_4021309 : Nat := 1376576251500741562495895

theorem tailTrace_4021309 : CollatzResearch.WordTrace tailWord_4021309 prefixEnd_4021309 1376576251500741562495895 := by
  unfold tailWord_4021309
  simp only [CollatzResearch.WordTrace]
  refine ⟨146669188588491752744570981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97779459058994501829713987 146669188588491752744570981)
  ·
    refine ⟨27500472860342203639607059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146669188588491752744570981 27500472860342203639607059)
    ·
      refine ⟨41250709290513305459410589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500472860342203639607059 41250709290513305459410589)
      ·
        refine ⟨15469015983942489547278971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41250709290513305459410589 15469015983942489547278971)
        ·
          refine ⟨23203523975913734320918457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15469015983942489547278971 23203523975913734320918457)
          ·
            refine ⟨17402642981935300740688843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23203523975913734320918457 17402642981935300740688843)
            ·
              refine ⟨26103964472902951111033265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17402642981935300740688843 26103964472902951111033265)
              ·
                refine ⟨19577973354677213333274949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26103964472902951111033265 19577973354677213333274949)
                ·
                  refine ⟨3670870004001977499989053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19577973354677213333274949 3670870004001977499989053)
                  ·
                    refine ⟨1376576251500741562495895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670870004001977499989053 1376576251500741562495895)
                    ·
                      rfl

theorem cell22_4021309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_4021309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021309 prefixEnd_4021309 := by exact prefixLift 4021309
  have htrace : WordTrace (prefixWord ++ tailWord_4021309) baseStart_4021309 baseEnd_4021309 := by
    simpa [prefixWord, tailWord_4021309, baseEnd_4021309] using wordTrace_append hprefix tailTrace_4021309
  have hstable : (prefixWord ++ tailWord_4021309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021309).length < 2 ^ (prefixWord ++ tailWord_4021309).sum := by decide
  have hdescent : baseEnd_4021309 < baseStart_4021309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021399 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 2, 5]
def baseStart_4021399 : Nat := 118140960795 + 4021399 * 2 ^ 59
def prefixEnd_4021399 : Nat := 4983230072969 + 3 ^ 40 * 4021399 * 2
def baseEnd_4021399 : Nat := 1376607060340011327745619

theorem tailTrace_4021399 : CollatzResearch.WordTrace tailWord_4021399 prefixEnd_4021399 1376607060340011327745619 := by
  unfold tailWord_4021399
  simp only [CollatzResearch.WordTrace]
  refine ⟨146672471158165698115347251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97781647438777132076898167 146672471158165698115347251)
  ·
    refine ⟨220008706737248547173020877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146672471158165698115347251 220008706737248547173020877)
    ·
      refine ⟨82503265026468205189882829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220008706737248547173020877 82503265026468205189882829)
      ·
        refine ⟨30938724384925576946206061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82503265026468205189882829 30938724384925576946206061)
        ·
          refine ⟨11602021644347091354827273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30938724384925576946206061 11602021644347091354827273)
          ·
            refine ⟨8701516233260318516120455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11602021644347091354827273 8701516233260318516120455)
            ·
              refine ⟨13052274349890477774180683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701516233260318516120455 13052274349890477774180683)
              ·
                refine ⟨19578411524835716661271025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13052274349890477774180683 19578411524835716661271025)
                ·
                  refine ⟨14683808643626787495953269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19578411524835716661271025 14683808643626787495953269)
                  ·
                    refine ⟨1376607060340011327745619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14683808643626787495953269 1376607060340011327745619)
                    ·
                      rfl

theorem cell22_4021399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_4021399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021399 prefixEnd_4021399 := by exact prefixLift 4021399
  have htrace : WordTrace (prefixWord ++ tailWord_4021399) baseStart_4021399 baseEnd_4021399 := by
    simpa [prefixWord, tailWord_4021399, baseEnd_4021399] using wordTrace_append hprefix tailTrace_4021399
  have hstable : (prefixWord ++ tailWord_4021399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021399).length < 2 ^ (prefixWord ++ tailWord_4021399).sum := by decide
  have hdescent : baseEnd_4021399 < baseStart_4021399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021457 : List Nat := [1, 2, 2, 1, 2, 2, 1, 11]
def baseStart_4021457 : Nat := 118140960795 + 4021457 * 2 ^ 59
def prefixEnd_4021457 : Nat := 4983230072969 + 3 ^ 40 * 4021457 * 2
def baseEnd_4021457 : Nat := 152958546102813167755049

theorem tailTrace_4021457 : CollatzResearch.WordTrace tailWord_4021457 prefixEnd_4021457 152958546102813167755049 := by
  unfold tailWord_4021457
  simp only [CollatzResearch.WordTrace]
  refine ⟨146674586591955574020958625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97783057727970382680639083 146674586591955574020958625)
  ·
    refine ⟨110005939943966680515718969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146674586591955574020958625 110005939943966680515718969)
    ·
      refine ⟨82504454957975010386789227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110005939943966680515718969 82504454957975010386789227)
      ·
        refine ⟨123756682436962515580183841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82504454957975010386789227 123756682436962515580183841)
        ·
          refine ⟨92817511827721886685137881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123756682436962515580183841 92817511827721886685137881)
          ·
            refine ⟨69613133870791415013853411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92817511827721886685137881 69613133870791415013853411)
            ·
              refine ⟨104419700806187122520780117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69613133870791415013853411 104419700806187122520780117)
              ·
                refine ⟨152958546102813167755049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 104419700806187122520780117 152958546102813167755049)
                ·
                  rfl

theorem cell22_4021457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 11].length) (baseStart_4021457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021457 prefixEnd_4021457 := by exact prefixLift 4021457
  have htrace : WordTrace (prefixWord ++ tailWord_4021457) baseStart_4021457 baseEnd_4021457 := by
    simpa [prefixWord, tailWord_4021457, baseEnd_4021457] using wordTrace_append hprefix tailTrace_4021457
  have hstable : (prefixWord ++ tailWord_4021457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021457).length < 2 ^ (prefixWord ++ tailWord_4021457).sum := by decide
  have hdescent : baseEnd_4021457 < baseStart_4021457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021461 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_4021461 : Nat := 118140960795 + 4021461 * 2 ^ 59
def prefixEnd_4021461 : Nat := 4983230072969 + 3 ^ 40 * 4021461 * 2
def baseEnd_4021461 : Nat := 1376628284207063832695429

theorem tailTrace_4021461 : CollatzResearch.WordTrace tailWord_4021461 prefixEnd_4021461 1376628284207063832695429 := by
  unfold tailWord_4021461
  simp only [CollatzResearch.WordTrace]
  refine ⟨146674732483941082704104237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97783154989294055136069491 146674732483941082704104237)
  ·
    refine ⟨55003024681477906014039089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146674732483941082704104237 55003024681477906014039089)
    ·
      refine ⟨41252268511108429510529317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55003024681477906014039089 41252268511108429510529317)
      ·
        refine ⟨7734800345832830533224247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41252268511108429510529317 7734800345832830533224247)
        ·
          refine ⟨11602200518749245799836371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734800345832830533224247 11602200518749245799836371)
          ·
            refine ⟨17403300778123868699754557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602200518749245799836371 17403300778123868699754557)
            ·
              refine ⟨6526237791796450762407959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17403300778123868699754557 6526237791796450762407959)
              ·
                refine ⟨9789356687694676143611939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526237791796450762407959 9789356687694676143611939)
                ·
                  refine ⟨14684035031542014215417909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789356687694676143611939 14684035031542014215417909)
                  ·
                    refine ⟨1376628284207063832695429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14684035031542014215417909 1376628284207063832695429)
                    ·
                      rfl

theorem cell22_4021461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_4021461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021461 prefixEnd_4021461 := by exact prefixLift 4021461
  have htrace : WordTrace (prefixWord ++ tailWord_4021461) baseStart_4021461 baseEnd_4021461 := by
    simpa [prefixWord, tailWord_4021461, baseEnd_4021461] using wordTrace_append hprefix tailTrace_4021461
  have hstable : (prefixWord ++ tailWord_4021461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021461).length < 2 ^ (prefixWord ++ tailWord_4021461).sum := by decide
  have hdescent : baseEnd_4021461 < baseStart_4021461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021512 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 2, 3]
def baseStart_4021512 : Nat := 118140960795 + 4021512 * 2 ^ 59
def prefixEnd_4021512 : Nat := 4983230072969 + 3 ^ 40 * 4021512 * 2
def baseEnd_4021512 : Nat := 1376645742549316699670273

theorem tailTrace_4021512 : CollatzResearch.WordTrace tailWord_4021512 prefixEnd_4021512 1376645742549316699670273 := by
  unfold tailWord_4021512
  simp only [CollatzResearch.WordTrace]
  refine ⟨73338296303378159207105395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97784395071170878942807193 73338296303378159207105395)
  ·
    refine ⟨110007444455067238810658093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73338296303378159207105395 110007444455067238810658093)
    ·
      refine ⟨41252791670650214553996785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110007444455067238810658093 41252791670650214553996785)
      ·
        refine ⟨30939593752987660915497589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41252791670650214553996785 30939593752987660915497589)
        ·
          refine ⟨2900586914342593210827899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30939593752987660915497589 2900586914342593210827899)
          ·
            refine ⟨4350880371513889816241849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900586914342593210827899 4350880371513889816241849)
            ·
              refine ⟨3263160278635417362181387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350880371513889816241849 3263160278635417362181387)
              ·
                refine ⟨4894740417953126043272081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263160278635417362181387 4894740417953126043272081)
                ·
                  refine ⟨3671055313464844532454061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894740417953126043272081 3671055313464844532454061)
                  ·
                    refine ⟨1376645742549316699670273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671055313464844532454061 1376645742549316699670273)
                    ·
                      rfl

theorem cell22_4021512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_4021512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021512 prefixEnd_4021512 := by exact prefixLift 4021512
  have htrace : WordTrace (prefixWord ++ tailWord_4021512) baseStart_4021512 baseEnd_4021512 := by
    simpa [prefixWord, tailWord_4021512, baseEnd_4021512] using wordTrace_append hprefix tailTrace_4021512
  have hstable : (prefixWord ++ tailWord_4021512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021512).length < 2 ^ (prefixWord ++ tailWord_4021512).sum := by decide
  have hdescent : baseEnd_4021512 < baseStart_4021512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021557 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_4021557 : Nat := 118140960795 + 4021557 * 2 ^ 59
def prefixEnd_4021557 : Nat := 4983230072969 + 3 ^ 40 * 4021557 * 2
def baseEnd_4021557 : Nat := 1376661146968951582295135

theorem tailTrace_4021557 : CollatzResearch.WordTrace tailWord_4021557 prefixEnd_4021557 1376661146968951582295135 := by
  unfold tailWord_4021557
  simp only [CollatzResearch.WordTrace]
  refine ⟨146678233891593291099598925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97785489261062194066399283 146678233891593291099598925)
  ·
    refine ⟨55004337709347484162349597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146678233891593291099598925 55004337709347484162349597)
    ·
      refine ⟨20626626641005306560881099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55004337709347484162349597 20626626641005306560881099)
      ·
        refine ⟨30939939961507959841321649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20626626641005306560881099 30939939961507959841321649)
        ·
          refine ⟨23204954971130969880991237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30939939961507959841321649 23204954971130969880991237)
          ·
            refine ⟨4350929057087056852685857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23204954971130969880991237 4350929057087056852685857)
            ·
              refine ⟨3263196792815292639514393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350929057087056852685857 3263196792815292639514393)
              ·
                refine ⟨2447397594611469479635795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263196792815292639514393 2447397594611469479635795)
                ·
                  refine ⟨3671096391917204219453693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447397594611469479635795 3671096391917204219453693)
                  ·
                    refine ⟨1376661146968951582295135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671096391917204219453693 1376661146968951582295135)
                    ·
                      rfl

theorem cell22_4021557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_4021557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021557 prefixEnd_4021557 := by exact prefixLift 4021557
  have htrace : WordTrace (prefixWord ++ tailWord_4021557) baseStart_4021557 baseEnd_4021557 := by
    simpa [prefixWord, tailWord_4021557, baseEnd_4021557] using wordTrace_append hprefix tailTrace_4021557
  have hstable : (prefixWord ++ tailWord_4021557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021557).length < 2 ^ (prefixWord ++ tailWord_4021557).sum := by decide
  have hdescent : baseEnd_4021557 < baseStart_4021557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021566 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4021566 : Nat := 118140960795 + 4021566 * 2 ^ 59
def prefixEnd_4021566 : Nat := 4983230072969 + 3 ^ 40 * 4021566 * 2
def baseEnd_4021566 : Nat := 1376664227852878558820107

theorem tailTrace_4021566 : CollatzResearch.WordTrace tailWord_4021566 prefixEnd_4021566 1376664227852878558820107 := by
  unfold tailWord_4021566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18334820268570085704584569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97785708099040457091117701 18334820268570085704584569)
  ·
    refine ⟨13751115201427564278438427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18334820268570085704584569 13751115201427564278438427)
    ·
      refine ⟨20626672802141346417657641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13751115201427564278438427 20626672802141346417657641)
      ·
        refine ⟨15470004601606009813243231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20626672802141346417657641 15470004601606009813243231)
        ·
          refine ⟨23205006902409014719864847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15470004601606009813243231 23205006902409014719864847)
          ·
            refine ⟨34807510353613522079797271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23205006902409014719864847 34807510353613522079797271)
            ·
              refine ⟨52211265530420283119695907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34807510353613522079797271 52211265530420283119695907)
              ·
                refine ⟨78316898295630424679543861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52211265530420283119695907 78316898295630424679543861)
                ·
                  refine ⟨7342209215215352313707237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78316898295630424679543861 7342209215215352313707237)
                  ·
                    refine ⟨1376664227852878558820107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7342209215215352313707237 1376664227852878558820107)
                    ·
                      rfl

theorem cell22_4021566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4021566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021566 prefixEnd_4021566 := by exact prefixLift 4021566
  have htrace : WordTrace (prefixWord ++ tailWord_4021566) baseStart_4021566 baseEnd_4021566 := by
    simpa [prefixWord, tailWord_4021566, baseEnd_4021566] using wordTrace_append hprefix tailTrace_4021566
  have hstable : (prefixWord ++ tailWord_4021566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021566).length < 2 ^ (prefixWord ++ tailWord_4021566).sum := by decide
  have hdescent : baseEnd_4021566 < baseStart_4021566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021600 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 1, 4]
def baseStart_4021600 : Nat := 118140960795 + 4021600 * 2 ^ 59
def prefixEnd_4021600 : Nat := 4983230072969 + 3 ^ 40 * 4021600 * 2
def baseEnd_4021600 : Nat := 1376675866747713803470003

theorem tailTrace_4021600 : CollatzResearch.WordTrace tailWord_4021600 prefixEnd_4021600 1376675866747713803470003 := by
  unfold tailWord_4021600
  simp only [CollatzResearch.WordTrace]
  refine ⟨73339901115218754721707127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97786534820291672962276169 73339901115218754721707127)
  ·
    refine ⟨110009851672828132082560691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73339901115218754721707127 110009851672828132082560691)
    ·
      refine ⟨165014777509242198123841037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110009851672828132082560691 165014777509242198123841037)
      ·
        refine ⟨61880541565965824296440389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165014777509242198123841037 61880541565965824296440389)
        ·
          refine ⟨11602601543618592055582573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61880541565965824296440389 11602601543618592055582573)
          ·
            refine ⟨4350975578856972020843465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11602601543618592055582573 4350975578856972020843465)
            ·
              refine ⟨3263231684142729015632599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350975578856972020843465 3263231684142729015632599)
              ·
                refine ⟨4894847526214093523448899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263231684142729015632599 4894847526214093523448899)
                ·
                  refine ⟨7342271289321140285173349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894847526214093523448899 7342271289321140285173349)
                  ·
                    refine ⟨1376675866747713803470003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7342271289321140285173349 1376675866747713803470003)
                    ·
                      rfl

theorem cell22_4021600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_4021600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021600 prefixEnd_4021600 := by exact prefixLift 4021600
  have htrace : WordTrace (prefixWord ++ tailWord_4021600) baseStart_4021600 baseEnd_4021600 := by
    simpa [prefixWord, tailWord_4021600, baseEnd_4021600] using wordTrace_append hprefix tailTrace_4021600
  have hstable : (prefixWord ++ tailWord_4021600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021600).length < 2 ^ (prefixWord ++ tailWord_4021600).sum := by decide
  have hdescent : baseEnd_4021600 < baseStart_4021600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021613 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_4021613 : Nat := 118140960795 + 4021613 * 2 ^ 59
def prefixEnd_4021613 : Nat := 4983230072969 + 3 ^ 40 * 4021613 * 2
def baseEnd_4021613 : Nat := 1376680316913386102894963

theorem tailTrace_4021613 : CollatzResearch.WordTrace tailWord_4021613 prefixEnd_4021613 1376680316913386102894963 := by
  unfold tailWord_4021613
  simp only [CollatzResearch.WordTrace]
  refine ⟨146680276379390412663637493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97786850919593608442424995 146680276379390412663637493)
  ·
    refine ⟨13751275910567851187216015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146680276379390412663637493 13751275910567851187216015)
    ·
      refine ⟨20626913865851776780824023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13751275910567851187216015 20626913865851776780824023)
      ·
        refine ⟨30940370798777665171236035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20626913865851776780824023 30940370798777665171236035)
        ·
          refine ⟨46410556198166497756854053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30940370798777665171236035 46410556198166497756854053)
          ·
            refine ⟨8701979287156218329410135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46410556198166497756854053 8701979287156218329410135)
            ·
              refine ⟨13052968930734327494115203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701979287156218329410135 13052968930734327494115203)
              ·
                refine ⟨19579453396101491241172805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13052968930734327494115203 19579453396101491241172805)
                ·
                  refine ⟨3671147511769029607719901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19579453396101491241172805 3671147511769029607719901)
                  ·
                    refine ⟨1376680316913386102894963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671147511769029607719901 1376680316913386102894963)
                    ·
                      rfl

theorem cell22_4021613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_4021613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021613 prefixEnd_4021613 := by exact prefixLift 4021613
  have htrace : WordTrace (prefixWord ++ tailWord_4021613) baseStart_4021613 baseEnd_4021613 := by
    simpa [prefixWord, tailWord_4021613, baseEnd_4021613] using wordTrace_append hprefix tailTrace_4021613
  have hstable : (prefixWord ++ tailWord_4021613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021613).length < 2 ^ (prefixWord ++ tailWord_4021613).sum := by decide
  have hdescent : baseEnd_4021613 < baseStart_4021613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021660 : List Nat := [2, 2, 3, 4, 2, 1, 8]
def baseStart_4021660 : Nat := 118140960795 + 4021660 * 2 ^ 59
def prefixEnd_4021660 : Nat := 4983230072969 + 3 ^ 40 * 4021660 * 2
def baseEnd_4021660 : Nat := 50988755776810875813697

theorem tailTrace_4021660 : CollatzResearch.WordTrace tailWord_4021660 prefixEnd_4021660 50988755776810875813697 := by
  unfold tailWord_4021660
  simp only [CollatzResearch.WordTrace]
  refine ⟨73340995305110069845299217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97787993740146759793732289 73340995305110069845299217)
  ·
    refine ⟨55005746478832552383974413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73340995305110069845299217 55005746478832552383974413)
    ·
      refine ⟨20627154929562207143990405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55005746478832552383974413 20627154929562207143990405)
      ·
        refine ⟨3867591549292913839498201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20627154929562207143990405 3867591549292913839498201)
        ·
          refine ⟨2900693661969685379623651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867591549292913839498201 2900693661969685379623651)
          ·
            refine ⟨4351040492954528069435477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900693661969685379623651 4351040492954528069435477)
            ·
              refine ⟨50988755776810875813697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4351040492954528069435477 50988755776810875813697)
              ·
                rfl

theorem cell22_4021660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 8].length) (baseStart_4021660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021660 prefixEnd_4021660 := by exact prefixLift 4021660
  have htrace : WordTrace (prefixWord ++ tailWord_4021660) baseStart_4021660 baseEnd_4021660 := by
    simpa [prefixWord, tailWord_4021660, baseEnd_4021660] using wordTrace_append hprefix tailTrace_4021660
  have hstable : (prefixWord ++ tailWord_4021660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021660).length < 2 ^ (prefixWord ++ tailWord_4021660).sum := by decide
  have hdescent : baseEnd_4021660 < baseStart_4021660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021671 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 7]
def baseStart_4021671 : Nat := 118140960795 + 4021671 * 2 ^ 59
def prefixEnd_4021671 : Nat := 4983230072969 + 3 ^ 40 * 4021671 * 2
def baseEnd_4021671 : Nat := 458900057166231094981595

theorem tailTrace_4021671 : CollatzResearch.WordTrace tailWord_4021671 prefixEnd_4021671 458900057166231094981595 := by
  unfold tailWord_4021671
  simp only [CollatzResearch.WordTrace]
  refine ⟨146682391813180288569248867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97788261208786859046165911 146682391813180288569248867)
  ·
    refine ⟨220023587719770432853873301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146682391813180288569248867 220023587719770432853873301)
    ·
      refine ⟨10313605674364239040025311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220023587719770432853873301 10313605674364239040025311)
      ·
        refine ⟨15470408511546358560037967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10313605674364239040025311 15470408511546358560037967)
        ·
          refine ⟨23205612767319537840056951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15470408511546358560037967 23205612767319537840056951)
          ·
            refine ⟨34808419150979306760085427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23205612767319537840056951 34808419150979306760085427)
            ·
              refine ⟨52212628726468960140128141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34808419150979306760085427 52212628726468960140128141)
              ·
                refine ⟨19579735772425860052548053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52212628726468960140128141 19579735772425860052548053)
                ·
                  refine ⟨458900057166231094981595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19579735772425860052548053 458900057166231094981595)
                  ·
                    rfl

theorem cell22_4021671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 7].length) (baseStart_4021671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021671 prefixEnd_4021671 := by exact prefixLift 4021671
  have htrace : WordTrace (prefixWord ++ tailWord_4021671) baseStart_4021671 baseEnd_4021671 := by
    simpa [prefixWord, tailWord_4021671, baseEnd_4021671] using wordTrace_append hprefix tailTrace_4021671
  have hstable : (prefixWord ++ tailWord_4021671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021671).length < 2 ^ (prefixWord ++ tailWord_4021671).sum := by decide
  have hdescent : baseEnd_4021671 < baseStart_4021671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021688 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 5]
def baseStart_4021688 : Nat := 118140960795 + 4021688 * 2 ^ 59
def prefixEnd_4021688 : Nat := 4983230072969 + 3 ^ 40 * 4021688 * 2
def baseEnd_4021688 : Nat := 458901996982036969089911

theorem tailTrace_4021688 : CollatzResearch.WordTrace tailWord_4021688 prefixEnd_4021688 458901996982036969089911 := by
  unfold tailWord_4021688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73341505927059350236308859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97788674569412466981745145 73341505927059350236308859)
  ·
    refine ⟨110012258890589025354463289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73341505927059350236308859 110012258890589025354463289)
    ·
      refine ⟨82509194167941769015847467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110012258890589025354463289 82509194167941769015847467)
      ·
        refine ⟨123763791251912653523771201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82509194167941769015847467 123763791251912653523771201)
        ·
          refine ⟨92822843438934490142828401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123763791251912653523771201 92822843438934490142828401)
          ·
            refine ⟨69617132579200867607121301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92822843438934490142828401 69617132579200867607121301)
            ·
              refine ⟨3263303089650040669083811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69617132579200867607121301 3263303089650040669083811)
              ·
                refine ⟨4894954634475061003625717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263303089650040669083811 4894954634475061003625717)
                ·
                  refine ⟨458901996982036969089911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4894954634475061003625717 458901996982036969089911)
                  ·
                    rfl

theorem cell22_4021688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_4021688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021688 prefixEnd_4021688 := by exact prefixLift 4021688
  have htrace : WordTrace (prefixWord ++ tailWord_4021688) baseStart_4021688 baseEnd_4021688 := by
    simpa [prefixWord, tailWord_4021688, baseEnd_4021688] using wordTrace_append hprefix tailTrace_4021688
  have hstable : (prefixWord ++ tailWord_4021688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021688).length < 2 ^ (prefixWord ++ tailWord_4021688).sum := by decide
  have hdescent : baseEnd_4021688 < baseStart_4021688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021791 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_4021791 : Nat := 118140960795 + 4021791 * 2 ^ 59
def prefixEnd_4021791 : Nat := 4983230072969 + 3 ^ 40 * 4021791 * 2
def baseEnd_4021791 : Nat := 1376741249951052971944417

theorem tailTrace_4021791 : CollatzResearch.WordTrace tailWord_4021791 prefixEnd_4021791 1376741249951052971944417 := by
  unfold tailWord_4021791
  simp only [CollatzResearch.WordTrace]
  refine ⟨146686768572745549063617227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97791179048497032709078151 146686768572745549063617227)
  ·
    refine ⟨220030152859118323595425841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146686768572745549063617227 220030152859118323595425841)
    ·
      refine ⟨165022614644338742696569381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220030152859118323595425841 165022614644338742696569381)
      ·
        refine ⟨30941740245813514255606759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165022614644338742696569381 30941740245813514255606759)
        ·
          refine ⟨46412610368720271383410139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30941740245813514255606759 46412610368720271383410139)
          ·
            refine ⟨69618915553080407075115209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46412610368720271383410139 69618915553080407075115209)
            ·
              refine ⟨52214186664810305306336407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69618915553080407075115209 52214186664810305306336407)
              ·
                refine ⟨78321279997215457959504611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52214186664810305306336407 78321279997215457959504611)
                ·
                  refine ⟨117481919995823186939256917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78321279997215457959504611 117481919995823186939256917)
                  ·
                    refine ⟨1376741249951052971944417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117481919995823186939256917 1376741249951052971944417)
                    ·
                      rfl

theorem cell22_4021791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_4021791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021791 prefixEnd_4021791 := by exact prefixLift 4021791
  have htrace : WordTrace (prefixWord ++ tailWord_4021791) baseStart_4021791 baseEnd_4021791 := by
    simpa [prefixWord, tailWord_4021791, baseEnd_4021791] using wordTrace_append hprefix tailTrace_4021791
  have hstable : (prefixWord ++ tailWord_4021791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021791).length < 2 ^ (prefixWord ++ tailWord_4021791).sum := by decide
  have hdescent : baseEnd_4021791 < baseStart_4021791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021844 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4021844 : Nat := 118140960795 + 4021844 * 2 ^ 59
def prefixEnd_4021844 : Nat := 4983230072969 + 3 ^ 40 * 4021844 * 2
def baseEnd_4021844 : Nat := 1376759392934178500369255

theorem tailTrace_4021844 : CollatzResearch.WordTrace tailWord_4021844 prefixEnd_4021844 1376759392934178500369255 := by
  unfold tailWord_4021844
  simp only [CollatzResearch.WordTrace]
  refine ⟨73344350820776769557648293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97792467761035692743531057 73344350820776769557648293)
  ·
    refine ⟨13752065778895644292059055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73344350820776769557648293 13752065778895644292059055)
    ·
      refine ⟨20628098668343466438088583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13752065778895644292059055 20628098668343466438088583)
      ·
        refine ⟨30942148002515199657132875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20628098668343466438088583 30942148002515199657132875)
        ·
          refine ⟨46413222003772799485699313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30942148002515199657132875 46413222003772799485699313)
          ·
            refine ⟨34809916502829599614274485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46413222003772799485699313 34809916502829599614274485)
            ·
              refine ⟨3263429672140274963838233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34809916502829599614274485 3263429672140274963838233)
              ·
                refine ⟨2447572254105206222878675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263429672140274963838233 2447572254105206222878675)
                ·
                  refine ⟨3671358381157809334318013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447572254105206222878675 3671358381157809334318013)
                  ·
                    refine ⟨1376759392934178500369255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671358381157809334318013 1376759392934178500369255)
                    ·
                      rfl

theorem cell22_4021844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4021844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021844 prefixEnd_4021844 := by exact prefixLift 4021844
  have htrace : WordTrace (prefixWord ++ tailWord_4021844) baseStart_4021844 baseEnd_4021844 := by
    simpa [prefixWord, tailWord_4021844, baseEnd_4021844] using wordTrace_append hprefix tailTrace_4021844
  have hstable : (prefixWord ++ tailWord_4021844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021844).length < 2 ^ (prefixWord ++ tailWord_4021844).sum := by decide
  have hdescent : baseEnd_4021844 < baseStart_4021844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021883 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 1, 5]
def baseStart_4021883 : Nat := 118140960795 + 4021883 * 2 ^ 59
def prefixEnd_4021883 : Nat := 4983230072969 + 3 ^ 40 * 4021883 * 2
def baseEnd_4021883 : Nat := 1376772743431195398644135

theorem tailTrace_4021883 : CollatzResearch.WordTrace tailWord_4021883 prefixEnd_4021883 1376772743431195398644135 := by
  unfold tailWord_4021883
  simp only [CollatzResearch.WordTrace]
  refine ⟨146690124088412248775966303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97793416058941499183977535 146690124088412248775966303)
  ·
    refine ⟨220035186132618373163949455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146690124088412248775966303 220035186132618373163949455)
    ·
      refine ⟨330052779198927559745924183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220035186132618373163949455 330052779198927559745924183)
      ·
        refine ⟨495079168798391339618886275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330052779198927559745924183 495079168798391339618886275)
        ·
          refine ⟨742618753197587009428329413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495079168798391339618886275 742618753197587009428329413)
          ·
            refine ⟨139241016224547564267811765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 742618753197587009428329413 139241016224547564267811765)
            ·
              refine ⟨13053845271051334150107353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139241016224547564267811765 13053845271051334150107353)
              ·
                refine ⟨9790383953288500612580515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13053845271051334150107353 9790383953288500612580515)
                ·
                  refine ⟨14685575929932750918870773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9790383953288500612580515 14685575929932750918870773)
                  ·
                    refine ⟨1376772743431195398644135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14685575929932750918870773 1376772743431195398644135)
                    ·
                      rfl

theorem cell22_4021883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_4021883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021883 prefixEnd_4021883 := by exact prefixLift 4021883
  have htrace : WordTrace (prefixWord ++ tailWord_4021883) baseStart_4021883 baseEnd_4021883 := by
    simpa [prefixWord, tailWord_4021883, baseEnd_4021883] using wordTrace_append hprefix tailTrace_4021883
  have hstable : (prefixWord ++ tailWord_4021883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021883).length < 2 ^ (prefixWord ++ tailWord_4021883).sum := by decide
  have hdescent : baseEnd_4021883 < baseStart_4021883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021902 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_4021902 : Nat := 118140960795 + 4021902 * 2 ^ 59
def prefixEnd_4021902 : Nat := 4983230072969 + 3 ^ 40 * 4021902 * 2
def baseEnd_4021902 : Nat := 458926415839828560806359

theorem tailTrace_4021902 : CollatzResearch.WordTrace tailWord_4021902 prefixEnd_4021902 458926415839828560806359 := by
  unfold tailWord_4021902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336352134417926877613495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97793878050228943347271973 18336352134417926877613495)
  ·
    refine ⟨27504528201626890316420243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18336352134417926877613495 27504528201626890316420243)
    ·
      refine ⟨41256792302440335474630365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27504528201626890316420243 41256792302440335474630365)
      ·
        refine ⟨15471297113415125802986387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41256792302440335474630365 15471297113415125802986387)
        ·
          refine ⟨23206945670122688704479581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15471297113415125802986387 23206945670122688704479581)
          ·
            refine ⟨8702604626296008264179843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23206945670122688704479581 8702604626296008264179843)
            ·
              refine ⟨13053906939444012396269765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702604626296008264179843 13053906939444012396269765)
              ·
                refine ⟨2447607551145752324300581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13053906939444012396269765 2447607551145752324300581)
                ·
                  refine ⟨458926415839828560806359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2447607551145752324300581 458926415839828560806359)
                  ·
                    rfl

theorem cell22_4021902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_4021902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021902 prefixEnd_4021902 := by exact prefixLift 4021902
  have htrace : WordTrace (prefixWord ++ tailWord_4021902) baseStart_4021902 baseEnd_4021902 := by
    simpa [prefixWord, tailWord_4021902, baseEnd_4021902] using wordTrace_append hprefix tailTrace_4021902
  have hstable : (prefixWord ++ tailWord_4021902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021902).length < 2 ^ (prefixWord ++ tailWord_4021902).sum := by decide
  have hdescent : baseEnd_4021902 < baseStart_4021902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021981 : List Nat := [1, 4, 3, 3, 2, 1, 2, 6]
def baseStart_4021981 : Nat := 118140960795 + 4021981 * 2 ^ 59
def prefixEnd_4021981 : Nat := 4983230072969 + 3 ^ 40 * 4021981 * 2
def baseEnd_4021981 : Nat := 152978476759328423299315

theorem tailTrace_4021981 : CollatzResearch.WordTrace tailWord_4021981 prefixEnd_4021981 152978476759328423299315 := by
  unfold tailWord_4021981
  simp only [CollatzResearch.WordTrace]
  refine ⟨146693698442057211513033797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97795798961371474342022531 146693698442057211513033797)
  ·
    refine ⟨27505068457885727158693837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146693698442057211513033797 27505068457885727158693837)
    ·
      refine ⟨10314400671707147684510189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27505068457885727158693837 10314400671707147684510189)
      ·
        refine ⟨3867900251890180381691321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10314400671707147684510189 3867900251890180381691321)
        ·
          refine ⟨2900925188917635286268491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867900251890180381691321 2900925188917635286268491)
          ·
            refine ⟨4351387783376452929402737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900925188917635286268491 4351387783376452929402737)
            ·
              refine ⟨3263540837532339697052053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4351387783376452929402737 3263540837532339697052053)
              ·
                refine ⟨152978476759328423299315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3263540837532339697052053 152978476759328423299315)
                ·
                  rfl

theorem cell22_4021981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 6].length) (baseStart_4021981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4021981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4021981 prefixEnd_4021981 := by exact prefixLift 4021981
  have htrace : WordTrace (prefixWord ++ tailWord_4021981) baseStart_4021981 baseEnd_4021981 := by
    simpa [prefixWord, tailWord_4021981, baseEnd_4021981] using wordTrace_append hprefix tailTrace_4021981
  have hstable : (prefixWord ++ tailWord_4021981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021981).length < 2 ^ (prefixWord ++ tailWord_4021981).sum := by decide
  have hdescent : baseEnd_4021981 < baseStart_4021981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022003 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 8]
def baseStart_4022003 : Nat := 118140960795 + 4022003 * 2 ^ 59
def prefixEnd_4022003 : Nat := 4983230072969 + 3 ^ 40 * 4022003 * 2
def baseEnd_4022003 : Nat := 458937940627851695214589

theorem tailTrace_4022003 : CollatzResearch.WordTrace tailWord_4022003 prefixEnd_4022003 458937940627851695214589 := by
  unfold tailWord_4022003
  simp only [CollatzResearch.WordTrace]
  refine ⟨146694500847977509270334663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97796333898651672846889775 146694500847977509270334663)
  ·
    refine ⟨220041751271966263905501995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146694500847977509270334663 220041751271966263905501995)
    ·
      refine ⟨330062626907949395858252993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220041751271966263905501995 330062626907949395858252993)
      ·
        refine ⟨247546970180962046893689745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330062626907949395858252993 247546970180962046893689745)
        ·
          refine ⟨185660227635721535170267309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247546970180962046893689745 185660227635721535170267309)
          ·
            refine ⟨69622585363395575688850241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185660227635721535170267309 69622585363395575688850241)
            ·
              refine ⟨52216939022546681766637681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69622585363395575688850241 52216939022546681766637681)
              ·
                refine ⟨39162704266910011324978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52216939022546681766637681 39162704266910011324978261)
                ·
                  refine ⟨458937940627851695214589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39162704266910011324978261 458937940627851695214589)
                  ·
                    rfl

theorem cell22_4022003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_4022003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022003 prefixEnd_4022003 := by exact prefixLift 4022003
  have htrace : WordTrace (prefixWord ++ tailWord_4022003) baseStart_4022003 baseEnd_4022003 := by
    simpa [prefixWord, tailWord_4022003, baseEnd_4022003] using wordTrace_append hprefix tailTrace_4022003
  have hstable : (prefixWord ++ tailWord_4022003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022003).length < 2 ^ (prefixWord ++ tailWord_4022003).sum := by decide
  have hdescent : baseEnd_4022003 < baseStart_4022003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022035 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 6, 3]
def baseStart_4022035 : Nat := 118140960795 + 4022035 * 2 ^ 59
def prefixEnd_4022035 : Nat := 4983230072969 + 3 ^ 40 * 4022035 * 2
def baseEnd_4022035 : Nat := 1376824776137517668843669

theorem tailTrace_4022035 : CollatzResearch.WordTrace tailWord_4022035 prefixEnd_4022035 1376824776137517668843669 := by
  unfold tailWord_4022035
  simp only [CollatzResearch.WordTrace]
  refine ⟨146695667983861578735499559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97797111989241052490333039 146695667983861578735499559)
  ·
    refine ⟨220043501975792368103249339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146695667983861578735499559 220043501975792368103249339)
    ·
      refine ⟨330065252963688552154874009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220043501975792368103249339 330065252963688552154874009)
      ·
        refine ⟨247548939722766414116155507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330065252963688552154874009 247548939722766414116155507)
        ·
          refine ⟨371323409584149621174233261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247548939722766414116155507 371323409584149621174233261)
          ·
            refine ⟨139246278594056107940337473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371323409584149621174233261 139246278594056107940337473)
            ·
              refine ⟨104434708945542080955253105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139246278594056107940337473 104434708945542080955253105)
              ·
                refine ⟨78326031709156560716439829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104434708945542080955253105 78326031709156560716439829)
                ·
                  refine ⟨3671532736366713783583117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78326031709156560716439829 3671532736366713783583117)
                  ·
                    refine ⟨1376824776137517668843669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671532736366713783583117 1376824776137517668843669)
                    ·
                      rfl

theorem cell22_4022035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 3].length) (baseStart_4022035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022035 prefixEnd_4022035 := by exact prefixLift 4022035
  have htrace : WordTrace (prefixWord ++ tailWord_4022035) baseStart_4022035 baseEnd_4022035 := by
    simpa [prefixWord, tailWord_4022035, baseEnd_4022035] using wordTrace_append hprefix tailTrace_4022035
  have hstable : (prefixWord ++ tailWord_4022035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022035).length < 2 ^ (prefixWord ++ tailWord_4022035).sum := by decide
  have hdescent : baseEnd_4022035 < baseStart_4022035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022039 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 1, 4]
def baseStart_4022039 : Nat := 118140960795 + 4022039 * 2 ^ 59
def prefixEnd_4022039 : Nat := 4983230072969 + 3 ^ 40 * 4022039 * 2
def baseEnd_4022039 : Nat := 1376826145419262991743657

theorem tailTrace_4022039 : CollatzResearch.WordTrace tailWord_4022039 prefixEnd_4022039 1376826145419262991743657 := by
  unfold tailWord_4022039
  simp only [CollatzResearch.WordTrace]
  refine ⟨146695813875847087418645171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97797209250564724945763447 146695813875847087418645171)
  ·
    refine ⟨220043720813770631127967757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146695813875847087418645171 220043720813770631127967757)
    ·
      refine ⟨82516395305163986672987909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220043720813770631127967757 82516395305163986672987909)
      ·
        refine ⟨15471824119718247501185233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82516395305163986672987909 15471824119718247501185233)
        ·
          refine ⟨11603868089788685625888925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15471824119718247501185233 11603868089788685625888925)
          ·
            refine ⟨4351450533670757109708347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11603868089788685625888925 4351450533670757109708347)
            ·
              refine ⟨6527175800506135664562521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351450533670757109708347 6527175800506135664562521)
              ·
                refine ⟨4895381850379601748421891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527175800506135664562521 4895381850379601748421891)
                ·
                  refine ⟨7343072775569402622632837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895381850379601748421891 7343072775569402622632837)
                  ·
                    refine ⟨1376826145419262991743657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7343072775569402622632837 1376826145419262991743657)
                    ·
                      rfl

theorem cell22_4022039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_4022039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022039 prefixEnd_4022039 := by exact prefixLift 4022039
  have htrace : WordTrace (prefixWord ++ tailWord_4022039) baseStart_4022039 baseEnd_4022039 := by
    simpa [prefixWord, tailWord_4022039, baseEnd_4022039] using wordTrace_append hprefix tailTrace_4022039
  have hstable : (prefixWord ++ tailWord_4022039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022039).length < 2 ^ (prefixWord ++ tailWord_4022039).sum := by decide
  have hdescent : baseEnd_4022039 < baseStart_4022039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022052 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_4022052 : Nat := 118140960795 + 4022052 * 2 ^ 59
def prefixEnd_4022052 : Nat := 4983230072969 + 3 ^ 40 * 4022052 * 2
def baseEnd_4022052 : Nat := 1376830595584935291168617

theorem tailTrace_4022052 : CollatzResearch.WordTrace tailWord_4022052 prefixEnd_4022052 1376830595584935291168617 := by
  unfold tailWord_4022052
  simp only [CollatzResearch.WordTrace]
  refine ⟨73348144012399995319434205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97797525349866660425912273 73348144012399995319434205)
  ·
    refine ⟨27505554004649998244787827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73348144012399995319434205 27505554004649998244787827)
    ·
      refine ⟨41258331006974997367181741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27505554004649998244787827 41258331006974997367181741)
      ·
        refine ⟨15471874127615624012693153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41258331006974997367181741 15471874127615624012693153)
        ·
          refine ⟨11603905595711718009519865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15471874127615624012693153 11603905595711718009519865)
          ·
            refine ⟨8702929196783788507139899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11603905595711718009519865 8702929196783788507139899)
            ·
              refine ⟨13054393795175682760709849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702929196783788507139899 13054393795175682760709849)
              ·
                refine ⟨9790795346381762070532387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13054393795175682760709849 9790795346381762070532387)
                ·
                  refine ⟨14686193019572643105798581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9790795346381762070532387 14686193019572643105798581)
                  ·
                    refine ⟨1376830595584935291168617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14686193019572643105798581 1376830595584935291168617)
                    ·
                      rfl

theorem cell22_4022052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_4022052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022052 prefixEnd_4022052 := by exact prefixLift 4022052
  have htrace : WordTrace (prefixWord ++ tailWord_4022052) baseStart_4022052 baseEnd_4022052 := by
    simpa [prefixWord, tailWord_4022052, baseEnd_4022052] using wordTrace_append hprefix tailTrace_4022052
  have hstable : (prefixWord ++ tailWord_4022052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022052).length < 2 ^ (prefixWord ++ tailWord_4022052).sum := by decide
  have hdescent : baseEnd_4022052 < baseStart_4022052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022086 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4022086 : Nat := 118140960795 + 4022086 * 2 ^ 59
def prefixEnd_4022086 : Nat := 4983230072969 + 3 ^ 40 * 4022086 * 2
def baseEnd_4022086 : Nat := 1376842234479770535818513

theorem tailTrace_4022086 : CollatzResearch.WordTrace tailWord_4022086 prefixEnd_4022086 1376842234479770535818513 := by
  unfold tailWord_4022086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584297753333650451425191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97798352071117876297070741 4584297753333650451425191)
  ·
    refine ⟨6876446630000475677137787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4584297753333650451425191 6876446630000475677137787)
    ·
      refine ⟨10314669945000713515706681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6876446630000475677137787 10314669945000713515706681)
      ·
        refine ⟨7736002458750535136780011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10314669945000713515706681 7736002458750535136780011)
        ·
          refine ⟨11604003688125802705170017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736002458750535136780011 11604003688125802705170017)
          ·
            refine ⟨8703002766094352028877513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11604003688125802705170017 8703002766094352028877513)
            ·
              refine ⟨6527252074570764021658135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8703002766094352028877513 6527252074570764021658135)
              ·
                refine ⟨9790878111856146032487203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527252074570764021658135 9790878111856146032487203)
                ·
                  refine ⟨14686317167784219048730805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9790878111856146032487203 14686317167784219048730805)
                  ·
                    refine ⟨1376842234479770535818513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14686317167784219048730805 1376842234479770535818513)
                    ·
                      rfl

theorem cell22_4022086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4022086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022086 prefixEnd_4022086 := by exact prefixLift 4022086
  have htrace : WordTrace (prefixWord ++ tailWord_4022086) baseStart_4022086 baseEnd_4022086 := by
    simpa [prefixWord, tailWord_4022086, baseEnd_4022086] using wordTrace_append hprefix tailTrace_4022086
  have hstable : (prefixWord ++ tailWord_4022086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022086).length < 2 ^ (prefixWord ++ tailWord_4022086).sum := by decide
  have hdescent : baseEnd_4022086 < baseStart_4022086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022097 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_4022097 : Nat := 118140960795 + 4022097 * 2 ^ 59
def prefixEnd_4022097 : Nat := 4983230072969 + 3 ^ 40 * 4022097 * 2
def baseEnd_4022097 : Nat := 1376846000004570173793479

theorem tailTrace_4022097 : CollatzResearch.WordTrace tailWord_4022097 prefixEnd_4022097 1376846000004570173793479 := by
  unfold tailWord_4022097
  simp only [CollatzResearch.WordTrace]
  refine ⟨146697929309636963324256545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97798619539757975549504363 146697929309636963324256545)
  ·
    refine ⟨110023446982227722493192409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146697929309636963324256545 110023446982227722493192409)
    ·
      refine ⟨82517585236670791869894307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110023446982227722493192409 82517585236670791869894307)
      ·
        refine ⟨123776377855006187804841461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82517585236670791869894307 123776377855006187804841461)
        ·
          refine ⟨11604035423906830106703887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123776377855006187804841461 11604035423906830106703887)
          ·
            refine ⟨17406053135860245160055831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604035423906830106703887 17406053135860245160055831)
            ·
              refine ⟨26109079703790367740083747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406053135860245160055831 26109079703790367740083747)
              ·
                refine ⟨39163619555685551610125621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26109079703790367740083747 39163619555685551610125621)
                ·
                  refine ⟨3671589333345520463449277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39163619555685551610125621 3671589333345520463449277)
                  ·
                    refine ⟨1376846000004570173793479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671589333345520463449277 1376846000004570173793479)
                    ·
                      rfl

theorem cell22_4022097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_4022097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022097 prefixEnd_4022097 := by exact prefixLift 4022097
  have htrace : WordTrace (prefixWord ++ tailWord_4022097) baseStart_4022097 baseEnd_4022097 := by
    simpa [prefixWord, tailWord_4022097, baseEnd_4022097] using wordTrace_append hprefix tailTrace_4022097
  have hstable : (prefixWord ++ tailWord_4022097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022097).length < 2 ^ (prefixWord ++ tailWord_4022097).sum := by decide
  have hdescent : baseEnd_4022097 < baseStart_4022097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022185 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_4022185 : Nat := 118140960795 + 4022185 * 2 ^ 59
def prefixEnd_4022185 : Nat := 4983230072969 + 3 ^ 40 * 4022185 * 2
def baseEnd_4022185 : Nat := 1376876124202967277593209

theorem tailTrace_4022185 : CollatzResearch.WordTrace tailWord_4022185 prefixEnd_4022185 1376876124202967277593209 := by
  unfold tailWord_4022185
  simp only [CollatzResearch.WordTrace]
  refine ⟨146701138933318154353460009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97800759288878769568973339 146701138933318154353460009)
  ·
    refine ⟨110025854199988615765095007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146701138933318154353460009 110025854199988615765095007)
    ·
      refine ⟨165038781299982923647642511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110025854199988615765095007 165038781299982923647642511)
      ·
        refine ⟨247558171949974385471463767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165038781299982923647642511 247558171949974385471463767)
        ·
          refine ⟨371337257924961578207195651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247558171949974385471463767 371337257924961578207195651)
          ·
            refine ⟨557005886887442367310793477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371337257924961578207195651 557005886887442367310793477)
            ·
              refine ⟨104438603791395443870773777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557005886887442367310793477 104438603791395443870773777)
              ·
                refine ⟨78328952843546582903080333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104438603791395443870773777 78328952843546582903080333)
                ·
                  refine ⟨29373357316329968588655125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78328952843546582903080333 29373357316329968588655125)
                  ·
                    refine ⟨1376876124202967277593209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29373357316329968588655125 1376876124202967277593209)
                    ·
                      rfl

theorem cell22_4022185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_4022185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022185 prefixEnd_4022185 := by exact prefixLift 4022185
  have htrace : WordTrace (prefixWord ++ tailWord_4022185) baseStart_4022185 baseEnd_4022185 := by
    simpa [prefixWord, tailWord_4022185, baseEnd_4022185] using wordTrace_append hprefix tailTrace_4022185
  have hstable : (prefixWord ++ tailWord_4022185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022185).length < 2 ^ (prefixWord ++ tailWord_4022185).sum := by decide
  have hdescent : baseEnd_4022185 < baseStart_4022185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022356 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_4022356 : Nat := 118140960795 + 4022356 * 2 ^ 59
def prefixEnd_4022356 : Nat := 4983230072969 + 3 ^ 40 * 4022356 * 2
def baseEnd_4022356 : Nat := 1376934660997579831567685

theorem tailTrace_4022356 : CollatzResearch.WordTrace tailWord_4022356 prefixEnd_4022356 1376934660997579831567685 := by
  unfold tailWord_4022356
  simp only [CollatzResearch.WordTrace]
  refine ⟨73353687907849325278967461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97804917210465767038623281 73353687907849325278967461)
  ·
    refine ⟨13753816482721748489806399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73353687907849325278967461 13753816482721748489806399)
    ·
      refine ⟨20630724724082622734709599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13753816482721748489806399 20630724724082622734709599)
      ·
        refine ⟨30946087086123934102064399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20630724724082622734709599 30946087086123934102064399)
        ·
          refine ⟨46419130629185901153096599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30946087086123934102064399 46419130629185901153096599)
          ·
            refine ⟨69628695943778851729644899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46419130629185901153096599 69628695943778851729644899)
            ·
              refine ⟨104443043915668277594467349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69628695943778851729644899 104443043915668277594467349)
              ·
                refine ⟨4895767683546950512240657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104443043915668277594467349 4895767683546950512240657)
                ·
                  refine ⟨3671825762660212884180493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4895767683546950512240657 3671825762660212884180493)
                  ·
                    refine ⟨1376934660997579831567685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671825762660212884180493 1376934660997579831567685)
                    ·
                      rfl

theorem cell22_4022356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_4022356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022356 prefixEnd_4022356 := by exact prefixLift 4022356
  have htrace : WordTrace (prefixWord ++ tailWord_4022356) baseStart_4022356 baseEnd_4022356 := by
    simpa [prefixWord, tailWord_4022356, baseEnd_4022356] using wordTrace_append hprefix tailTrace_4022356
  have hstable : (prefixWord ++ tailWord_4022356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022356).length < 2 ^ (prefixWord ++ tailWord_4022356).sum := by decide
  have hdescent : baseEnd_4022356 < baseStart_4022356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022358 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4022358 : Nat := 118140960795 + 4022358 * 2 ^ 59
def prefixEnd_4022358 : Nat := 4983230072969 + 3 ^ 40 * 4022358 * 2
def baseEnd_4022358 : Nat := 458978448546150831005893

theorem tailTrace_4022358 : CollatzResearch.WordTrace tailWord_4022358 prefixEnd_4022358 458978448546150831005893 := by
  unfold tailWord_4022358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169215547605712806219233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97804965841127603266338485 9169215547605712806219233)
  ·
    refine ⟨6876911660704284604664425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9169215547605712806219233 6876911660704284604664425)
    ·
      refine ⟨5157683745528213453498319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6876911660704284604664425 5157683745528213453498319)
      ·
        refine ⟨7736525618292320180247479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157683745528213453498319 7736525618292320180247479)
        ·
          refine ⟨11604788427438480270371219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736525618292320180247479 11604788427438480270371219)
          ·
            refine ⟨17407182641157720405556829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604788427438480270371219 17407182641157720405556829)
            ·
              refine ⟨6527693490434145152083811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17407182641157720405556829 6527693490434145152083811)
              ·
                refine ⟨9791540235651217728125717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527693490434145152083811 9791540235651217728125717)
                ·
                  refine ⟨458978448546150831005893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9791540235651217728125717 458978448546150831005893)
                  ·
                    rfl

theorem cell22_4022358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4022358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022358 prefixEnd_4022358 := by exact prefixLift 4022358
  have htrace : WordTrace (prefixWord ++ tailWord_4022358) baseStart_4022358 baseEnd_4022358 := by
    simpa [prefixWord, tailWord_4022358, baseEnd_4022358] using wordTrace_append hprefix tailTrace_4022358
  have hstable : (prefixWord ++ tailWord_4022358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022358).length < 2 ^ (prefixWord ++ tailWord_4022358).sum := by decide
  have hdescent : baseEnd_4022358 < baseStart_4022358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022367 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_4022367 : Nat := 118140960795 + 4022367 * 2 ^ 59
def prefixEnd_4022367 : Nat := 4983230072969 + 3 ^ 40 * 4022367 * 2
def baseEnd_4022367 : Nat := 1376938426522379469542651

theorem tailTrace_4022367 : CollatzResearch.WordTrace tailWord_4022367 prefixEnd_4022367 1376938426522379469542651 := by
  unfold tailWord_4022367
  simp only [CollatzResearch.WordTrace]
  refine ⟨146707777018658799436585355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97805184679105866291056903 146707777018658799436585355)
  ·
    refine ⟨220061665527988199154878033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146707777018658799436585355 220061665527988199154878033)
    ·
      refine ⟨165046249145991149366158525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220061665527988199154878033 165046249145991149366158525)
      ·
        refine ⟨61892343429746681012309447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165046249145991149366158525 61892343429746681012309447)
        ·
          refine ⟨92838515144620021518464171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61892343429746681012309447 92838515144620021518464171)
          ·
            refine ⟨139257772716930032277696257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92838515144620021518464171 139257772716930032277696257)
            ·
              refine ⟨104443329537697524208272193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139257772716930032277696257 104443329537697524208272193)
              ·
                refine ⟨78332497153273143156204145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104443329537697524208272193 78332497153273143156204145)
                ·
                  refine ⟨58749372864954857367153109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78332497153273143156204145 58749372864954857367153109)
                  ·
                    refine ⟨1376938426522379469542651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58749372864954857367153109 1376938426522379469542651)
                    ·
                      rfl

theorem cell22_4022367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_4022367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022367 prefixEnd_4022367 := by exact prefixLift 4022367
  have htrace : WordTrace (prefixWord ++ tailWord_4022367) baseStart_4022367 baseEnd_4022367 := by
    simpa [prefixWord, tailWord_4022367, baseEnd_4022367] using wordTrace_append hprefix tailTrace_4022367
  have hstable : (prefixWord ++ tailWord_4022367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022367).length < 2 ^ (prefixWord ++ tailWord_4022367).sum := by decide
  have hdescent : baseEnd_4022367 < baseStart_4022367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022373 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_4022373 : Nat := 118140960795 + 4022373 * 2 ^ 59
def prefixEnd_4022373 : Nat := 4983230072969 + 3 ^ 40 * 4022373 * 2
def baseEnd_4022373 : Nat := 1376940480444997453892633

theorem tailTrace_4022373 : CollatzResearch.WordTrace tailWord_4022373 prefixEnd_4022373 1376940480444997453892633 := by
  unfold tailWord_4022373
  simp only [CollatzResearch.WordTrace]
  refine ⟨146707995856637062461303773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97805330571091374974202515 146707995856637062461303773)
  ·
    refine ⟨55015498446238898422988915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146707995856637062461303773 55015498446238898422988915)
    ·
      refine ⟨82523247669358347634483373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55015498446238898422988915 82523247669358347634483373)
      ·
        refine ⟨30946217876009380362931265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82523247669358347634483373 30946217876009380362931265)
        ·
          refine ⟨23209663407007035272198449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30946217876009380362931265 23209663407007035272198449)
          ·
            refine ⟨17407247555255276454148837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23209663407007035272198449 17407247555255276454148837)
            ·
              refine ⟨3263858916610364335152907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17407247555255276454148837 3263858916610364335152907)
              ·
                refine ⟨4895788374915546502729361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263858916610364335152907 4895788374915546502729361)
                ·
                  refine ⟨3671841281186659877047021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4895788374915546502729361 3671841281186659877047021)
                  ·
                    refine ⟨1376940480444997453892633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671841281186659877047021 1376940480444997453892633)
                    ·
                      rfl

theorem cell22_4022373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_4022373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022373 prefixEnd_4022373 := by exact prefixLift 4022373
  have htrace : WordTrace (prefixWord ++ tailWord_4022373) baseStart_4022373 baseEnd_4022373 := by
    simpa [prefixWord, tailWord_4022373, baseEnd_4022373] using wordTrace_append hprefix tailTrace_4022373
  have hstable : (prefixWord ++ tailWord_4022373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022373).length < 2 ^ (prefixWord ++ tailWord_4022373).sum := by decide
  have hdescent : baseEnd_4022373 < baseStart_4022373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022420 : List Nat := [2, 4, 2, 3, 2, 1, 1, 7]
def baseStart_4022420 : Nat := 118140960795 + 4022420 * 2 ^ 59
def prefixEnd_4022420 : Nat := 4983230072969 + 3 ^ 40 * 4022420 * 2
def baseEnd_4022420 : Nat := 152995174389500555329721

theorem tailTrace_4022420 : CollatzResearch.WordTrace tailWord_4022420 prefixEnd_4022420 152995174389500555329721 := by
  unfold tailWord_4022420
  simp only [CollatzResearch.WordTrace]
  refine ⟨73354855043733394744132357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97806473391644526325509809 73354855043733394744132357)
  ·
    refine ⟨13754035320700011514524817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73354855043733394744132357 13754035320700011514524817)
    ·
      refine ⟨10315526490525008635893613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13754035320700011514524817 10315526490525008635893613)
      ·
        refine ⟨3868322433946878238460105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10315526490525008635893613 3868322433946878238460105)
        ·
          refine ⟨2901241825460158678845079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3868322433946878238460105 2901241825460158678845079)
          ·
            refine ⟨4351862738190238018267619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901241825460158678845079 4351862738190238018267619)
            ·
              refine ⟨6527794107285357027401429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351862738190238018267619 6527794107285357027401429)
              ·
                refine ⟨152995174389500555329721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6527794107285357027401429 152995174389500555329721)
                ·
                  rfl

theorem cell22_4022420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 7].length) (baseStart_4022420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022420 prefixEnd_4022420 := by exact prefixLift 4022420
  have htrace : WordTrace (prefixWord ++ tailWord_4022420) baseStart_4022420 baseEnd_4022420 := by
    simpa [prefixWord, tailWord_4022420, baseEnd_4022420] using wordTrace_append hprefix tailTrace_4022420
  have hstable : (prefixWord ++ tailWord_4022420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022420).length < 2 ^ (prefixWord ++ tailWord_4022420).sum := by decide
  have hdescent : baseEnd_4022420 < baseStart_4022420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022429 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4022429 : Nat := 118140960795 + 4022429 * 2 ^ 59
def prefixEnd_4022429 : Nat := 4983230072969 + 3 ^ 40 * 4022429 * 2
def baseEnd_4022429 : Nat := 1376959650389431974492461

theorem tailTrace_4022429 : CollatzResearch.WordTrace tailWord_4022429 prefixEnd_4022429 1376959650389431974492461 := by
  unfold tailWord_4022429
  simp only [CollatzResearch.WordTrace]
  refine ⟨146710038344434184025342341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97806692229622789350228227 146710038344434184025342341)
  ·
    refine ⟨27508132189581409504751689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146710038344434184025342341 27508132189581409504751689)
    ·
      refine ⟨20631099142186057128563767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27508132189581409504751689 20631099142186057128563767)
      ·
        refine ⟨30946648713279085692845651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20631099142186057128563767 30946648713279085692845651)
        ·
          refine ⟨46419973069918628539268477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30946648713279085692845651 46419973069918628539268477)
          ·
            refine ⟨17407489901219485702225679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46419973069918628539268477 17407489901219485702225679)
            ·
              refine ⟨26111234851829228553338519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17407489901219485702225679 26111234851829228553338519)
              ·
                refine ⟨39166852277743842830007779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26111234851829228553338519 39166852277743842830007779)
                ·
                  refine ⟨58750278416615764245011669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39166852277743842830007779 58750278416615764245011669)
                  ·
                    refine ⟨1376959650389431974492461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58750278416615764245011669 1376959650389431974492461)
                    ·
                      rfl

theorem cell22_4022429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4022429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022429 prefixEnd_4022429 := by exact prefixLift 4022429
  have htrace : WordTrace (prefixWord ++ tailWord_4022429) baseStart_4022429 baseEnd_4022429 := by
    simpa [prefixWord, tailWord_4022429, baseEnd_4022429] using wordTrace_append hprefix tailTrace_4022429
  have hstable : (prefixWord ++ tailWord_4022429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022429).length < 2 ^ (prefixWord ++ tailWord_4022429).sum := by decide
  have hdescent : baseEnd_4022429 < baseStart_4022429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022431 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 5]
def baseStart_4022431 : Nat := 118140960795 + 4022431 * 2 ^ 59
def prefixEnd_4022431 : Nat := 4983230072969 + 3 ^ 40 * 4022431 * 2
def baseEnd_4022431 : Nat := 458986778343434878647485

theorem tailTrace_4022431 : CollatzResearch.WordTrace tailWord_4022431 prefixEnd_4022431 458986778343434878647485 := by
  unfold tailWord_4022431
  simp only [CollatzResearch.WordTrace]
  refine ⟨146710111290426938366915147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97806740860284625577943431 146710111290426938366915147)
  ·
    refine ⟨220065166935640407550372721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146710111290426938366915147 220065166935640407550372721)
    ·
      refine ⟨165048875201730305662779541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220065166935640407550372721 165048875201730305662779541)
      ·
        refine ⟨7736666025081108077942791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165048875201730305662779541 7736666025081108077942791)
        ·
          refine ⟨11604999037621662116914187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736666025081108077942791 11604999037621662116914187)
          ·
            refine ⟨17407498556432493175371281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604999037621662116914187 17407498556432493175371281)
            ·
              refine ⟨13055623917324369881528461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17407498556432493175371281 13055623917324369881528461)
              ·
                refine ⟨4895858968996638705573173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13055623917324369881528461 4895858968996638705573173)
                ·
                  refine ⟨458986778343434878647485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4895858968996638705573173 458986778343434878647485)
                  ·
                    rfl

theorem cell22_4022431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 5].length) (baseStart_4022431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022431 prefixEnd_4022431 := by exact prefixLift 4022431
  have htrace : WordTrace (prefixWord ++ tailWord_4022431) baseStart_4022431 baseEnd_4022431 := by
    simpa [prefixWord, tailWord_4022431, baseEnd_4022431] using wordTrace_append hprefix tailTrace_4022431
  have hstable : (prefixWord ++ tailWord_4022431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022431).length < 2 ^ (prefixWord ++ tailWord_4022431).sum := by decide
  have hdescent : baseEnd_4022431 < baseStart_4022431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022465 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 5]
def baseStart_4022465 : Nat := 118140960795 + 4022465 * 2 ^ 59
def prefixEnd_4022465 : Nat := 4983230072969 + 3 ^ 40 * 4022465 * 2
def baseEnd_4022465 : Nat := 458990657975046626864117

theorem tailTrace_4022465 : CollatzResearch.WordTrace tailWord_4022465 prefixEnd_4022465 458990657975046626864117 := by
  unfold tailWord_4022465
  simp only [CollatzResearch.WordTrace]
  refine ⟨146711351372303762173652849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97807567581535841449101899 146711351372303762173652849)
  ·
    refine ⟨110033513529227821630239637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146711351372303762173652849 110033513529227821630239637)
    ·
      refine ⟨5157820946682554138917483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110033513529227821630239637 5157820946682554138917483)
      ·
        refine ⟨7736731420023831208376225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157820946682554138917483 7736731420023831208376225)
        ·
          refine ⟨5802548565017873406282169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7736731420023831208376225 5802548565017873406282169)
          ·
            refine ⟨4351911423763405054711627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5802548565017873406282169 4351911423763405054711627)
            ·
              refine ⟨6527867135645107582067441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351911423763405054711627 6527867135645107582067441)
              ·
                refine ⟨4895900351733830686550581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527867135645107582067441 4895900351733830686550581)
                ·
                  refine ⟨458990657975046626864117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4895900351733830686550581 458990657975046626864117)
                  ·
                    rfl

theorem cell22_4022465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_4022465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022465 prefixEnd_4022465 := by exact prefixLift 4022465
  have htrace : WordTrace (prefixWord ++ tailWord_4022465) baseStart_4022465 baseEnd_4022465 := by
    simpa [prefixWord, tailWord_4022465, baseEnd_4022465] using wordTrace_append hprefix tailTrace_4022465
  have hstable : (prefixWord ++ tailWord_4022465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022465).length < 2 ^ (prefixWord ++ tailWord_4022465).sum := by decide
  have hdescent : baseEnd_4022465 < baseStart_4022465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022489 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_4022489 : Nat := 118140960795 + 4022489 * 2 ^ 59
def prefixEnd_4022489 : Nat := 4983230072969 + 3 ^ 40 * 4022489 * 2
def baseEnd_4022489 : Nat := 1376980189615611817992277

theorem tailTrace_4022489 : CollatzResearch.WordTrace tailWord_4022489 prefixEnd_4022489 1376980189615611817992277 := by
  unfold tailWord_4022489
  simp only [CollatzResearch.WordTrace]
  refine ⟨146712226724216814272526521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97808151149477876181684347 146712226724216814272526521)
  ·
    refine ⟨110034170043162610704394891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146712226724216814272526521 110034170043162610704394891)
    ·
      refine ⟨165051255064743916056592337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110034170043162610704394891 165051255064743916056592337)
      ·
        refine ⟨123788441298557937042444253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165051255064743916056592337 123788441298557937042444253)
        ·
          refine ⟨46420665486959226390916595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123788441298557937042444253 46420665486959226390916595)
          ·
            refine ⟨69630998230438839586374893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46420665486959226390916595 69630998230438839586374893)
            ·
              refine ⟨26111624336414564844890585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69630998230438839586374893 26111624336414564844890585)
              ·
                refine ⟨19583718252310923633667939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26111624336414564844890585 19583718252310923633667939)
                ·
                  refine ⟨29375577378466385450501909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19583718252310923633667939 29375577378466385450501909)
                  ·
                    refine ⟨1376980189615611817992277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29375577378466385450501909 1376980189615611817992277)
                    ·
                      rfl

theorem cell22_4022489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_4022489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022489 prefixEnd_4022489 := by exact prefixLift 4022489
  have htrace : WordTrace (prefixWord ++ tailWord_4022489) baseStart_4022489 baseEnd_4022489 := by
    simpa [prefixWord, tailWord_4022489, baseEnd_4022489] using wordTrace_append hprefix tailTrace_4022489
  have hstable : (prefixWord ++ tailWord_4022489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022489).length < 2 ^ (prefixWord ++ tailWord_4022489).sum := by decide
  have hdescent : baseEnd_4022489 < baseStart_4022489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022506 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_4022506 : Nat := 118140960795 + 4022506 * 2 ^ 59
def prefixEnd_4022506 : Nat := 4983230072969 + 3 ^ 40 * 4022506 * 2
def baseEnd_4022506 : Nat := 1376986009063029440317225

theorem tailTrace_4022506 : CollatzResearch.WordTrace tailWord_4022506 prefixEnd_4022506 1376986009063029440317225 := by
  unfold tailWord_4022506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36678211691288806543973843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97808564510103484117263581 36678211691288806543973843)
  ·
    refine ⟨55017317536933209815960765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36678211691288806543973843 55017317536933209815960765)
    ·
      refine ⟨20631494076349953680985287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55017317536933209815960765 20631494076349953680985287)
      ·
        refine ⟨30947241114524930521477931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20631494076349953680985287 30947241114524930521477931)
        ·
          refine ⟨46420861671787395782216897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30947241114524930521477931 46420861671787395782216897)
          ·
            refine ⟨34815646253840546836662673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46420861671787395782216897 34815646253840546836662673)
            ·
              refine ⟨26111734690380410127497005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34815646253840546836662673 26111734690380410127497005)
              ·
                refine ⟨9791900508892653797811377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26111734690380410127497005 9791900508892653797811377)
                ·
                  refine ⟨7343925381669490348358533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9791900508892653797811377 7343925381669490348358533)
                  ·
                    refine ⟨1376986009063029440317225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7343925381669490348358533 1376986009063029440317225)
                    ·
                      rfl

theorem cell22_4022506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_4022506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022506 prefixEnd_4022506 := by exact prefixLift 4022506
  have htrace : WordTrace (prefixWord ++ tailWord_4022506) baseStart_4022506 baseEnd_4022506 := by
    simpa [prefixWord, tailWord_4022506, baseEnd_4022506] using wordTrace_append hprefix tailTrace_4022506
  have hstable : (prefixWord ++ tailWord_4022506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022506).length < 2 ^ (prefixWord ++ tailWord_4022506).sum := by decide
  have hdescent : baseEnd_4022506 < baseStart_4022506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022581 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4022581 : Nat := 118140960795 + 4022581 * 2 ^ 59
def prefixEnd_4022581 : Nat := 4983230072969 + 3 ^ 40 * 4022581 * 2
def baseEnd_4022581 : Nat := 1377011683095754244691995

theorem tailTrace_4022581 : CollatzResearch.WordTrace tailWord_4022581 prefixEnd_4022581 1377011683095754244691995 := by
  unfold tailWord_4022581
  simp only [CollatzResearch.WordTrace]
  refine ⟨146715582239883513984875597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97810388159922342656583731 146715582239883513984875597)
  ·
    refine ⟨55018343339956317744328349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146715582239883513984875597 55018343339956317744328349)
    ·
      refine ⟨20631878752483619154123131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55018343339956317744328349 20631878752483619154123131)
      ·
        refine ⟨30947818128725428731184697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20631878752483619154123131 30947818128725428731184697)
        ·
          refine ⟨23210863596544071548388523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30947818128725428731184697 23210863596544071548388523)
          ·
            refine ⟨34816295394816107322582785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23210863596544071548388523 34816295394816107322582785)
            ·
              refine ⟨26112221546112080491937089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34816295394816107322582785 26112221546112080491937089)
              ·
                refine ⟨19584166159584060368952817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26112221546112080491937089 19584166159584060368952817)
                ·
                  refine ⟨14688124619688045276714613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19584166159584060368952817 14688124619688045276714613)
                  ·
                    refine ⟨1377011683095754244691995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14688124619688045276714613 1377011683095754244691995)
                    ·
                      rfl

theorem cell22_4022581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4022581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022581 prefixEnd_4022581 := by exact prefixLift 4022581
  have htrace : WordTrace (prefixWord ++ tailWord_4022581) baseStart_4022581 baseEnd_4022581 := by
    simpa [prefixWord, tailWord_4022581, baseEnd_4022581] using wordTrace_append hprefix tailTrace_4022581
  have hstable : (prefixWord ++ tailWord_4022581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022581).length < 2 ^ (prefixWord ++ tailWord_4022581).sum := by decide
  have hdescent : baseEnd_4022581 < baseStart_4022581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022641 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_4022641 : Nat := 118140960795 + 4022641 * 2 ^ 59
def prefixEnd_4022641 : Nat := 4983230072969 + 3 ^ 40 * 4022641 * 2
def baseEnd_4022641 : Nat := 1377032222321934088191811

theorem tailTrace_4022641 : CollatzResearch.WordTrace tailWord_4022641 prefixEnd_4022641 1377032222321934088191811 := by
  unfold tailWord_4022641
  simp only [CollatzResearch.WordTrace]
  refine ⟨146717770619666144232059777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97811847079777429488039851 146717770619666144232059777)
  ·
    refine ⟨110038327964749608174044833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146717770619666144232059777 110038327964749608174044833)
    ·
      refine ⟨82528745973562206130533625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110038327964749608174044833 82528745973562206130533625)
      ·
        refine ⟨61896559480171654597900219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82528745973562206130533625 61896559480171654597900219)
        ·
          refine ⟨92844839220257481896850329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61896559480171654597900219 92844839220257481896850329)
          ·
            refine ⟨69633629415193111422637747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92844839220257481896850329 69633629415193111422637747)
            ·
              refine ⟨104450444122789667133956621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69633629415193111422637747 104450444122789667133956621)
              ·
                refine ⟨39168916546046125175233733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104450444122789667133956621 39168916546046125175233733)
                ·
                  refine ⟨7344171852383648470356325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39168916546046125175233733 7344171852383648470356325)
                  ·
                    refine ⟨1377032222321934088191811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7344171852383648470356325 1377032222321934088191811)
                    ·
                      rfl

theorem cell22_4022641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_4022641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022641 prefixEnd_4022641 := by exact prefixLift 4022641
  have htrace : WordTrace (prefixWord ++ tailWord_4022641) baseStart_4022641 baseEnd_4022641 := by
    simpa [prefixWord, tailWord_4022641, baseEnd_4022641] using wordTrace_append hprefix tailTrace_4022641
  have hstable : (prefixWord ++ tailWord_4022641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022641).length < 2 ^ (prefixWord ++ tailWord_4022641).sum := by decide
  have hdescent : baseEnd_4022641 < baseStart_4022641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022645 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 4]
def baseStart_4022645 : Nat := 118140960795 + 4022645 * 2 ^ 59
def prefixEnd_4022645 : Nat := 4983230072969 + 3 ^ 40 * 4022645 * 2
def baseEnd_4022645 : Nat := 459011197201226470363933

theorem tailTrace_4022645 : CollatzResearch.WordTrace tailWord_4022645 prefixEnd_4022645 459011197201226470363933 := by
  unfold tailWord_4022645
  simp only [CollatzResearch.WordTrace]
  refine ⟨146717916511651652915205389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97811944341101101943470259 146717916511651652915205389)
  ·
    refine ⟨55019218691869369843202021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146717916511651652915205389 55019218691869369843202021)
    ·
      refine ⟨10316103504725506845600379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55019218691869369843202021 10316103504725506845600379)
      ·
        refine ⟨15474155257088260268400569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10316103504725506845600379 15474155257088260268400569)
        ·
          refine ⟨11605616442816195201300427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15474155257088260268400569 11605616442816195201300427)
          ·
            refine ⟨17408424664224292801950641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11605616442816195201300427 17408424664224292801950641)
            ·
              refine ⟨13056318498168219601462981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17408424664224292801950641 13056318498168219601462981)
              ·
                refine ⟨2448059718406541175274309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13056318498168219601462981 2448059718406541175274309)
                ·
                  refine ⟨459011197201226470363933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448059718406541175274309 459011197201226470363933)
                  ·
                    rfl

theorem cell22_4022645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_4022645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022645 prefixEnd_4022645 := by exact prefixLift 4022645
  have htrace : WordTrace (prefixWord ++ tailWord_4022645) baseStart_4022645 baseEnd_4022645 := by
    simpa [prefixWord, tailWord_4022645, baseEnd_4022645] using wordTrace_append hprefix tailTrace_4022645
  have hstable : (prefixWord ++ tailWord_4022645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022645).length < 2 ^ (prefixWord ++ tailWord_4022645).sum := by decide
  have hdescent : baseEnd_4022645 < baseStart_4022645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022705 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_4022705 : Nat := 118140960795 + 4022705 * 2 ^ 59
def prefixEnd_4022705 : Nat := 4983230072969 + 3 ^ 40 * 4022705 * 2
def baseEnd_4022705 : Nat := 1377054130829859254591615

theorem tailTrace_4022705 : CollatzResearch.WordTrace tailWord_4022705 prefixEnd_4022705 1377054130829859254591615 := by
  unfold tailWord_4022705
  simp only [CollatzResearch.WordTrace]
  refine ⟨146720104891434283162389569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97813403260956188774926379 146720104891434283162389569)
  ·
    refine ⟨110040078668575712371792177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146720104891434283162389569 110040078668575712371792177)
    ·
      refine ⟨82530059001431784278844133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110040078668575712371792177 82530059001431784278844133)
      ·
        refine ⟨15474386062768459552283275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82530059001431784278844133 15474386062768459552283275)
        ·
          refine ⟨23211579094152689328424913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474386062768459552283275 23211579094152689328424913)
          ·
            refine ⟨17408684320614516996318685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23211579094152689328424913 17408684320614516996318685)
            ·
              refine ⟨6528256620230443873619507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17408684320614516996318685 6528256620230443873619507)
              ·
                refine ⟨9792384930345665810429261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528256620230443873619507 9792384930345665810429261)
                ·
                  refine ⟨3672144348879624678910973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9792384930345665810429261 3672144348879624678910973)
                  ·
                    refine ⟨1377054130829859254591615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672144348879624678910973 1377054130829859254591615)
                    ·
                      rfl

theorem cell22_4022705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_4022705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022705 prefixEnd_4022705 := by exact prefixLift 4022705
  have htrace : WordTrace (prefixWord ++ tailWord_4022705) baseStart_4022705 baseEnd_4022705 := by
    simpa [prefixWord, tailWord_4022705, baseEnd_4022705] using wordTrace_append hprefix tailTrace_4022705
  have hstable : (prefixWord ++ tailWord_4022705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022705).length < 2 ^ (prefixWord ++ tailWord_4022705).sum := by decide
  have hdescent : baseEnd_4022705 < baseStart_4022705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022765 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4022765 : Nat := 118140960795 + 4022765 * 2 ^ 59
def prefixEnd_4022765 : Nat := 4983230072969 + 3 ^ 40 * 4022765 * 2
def baseEnd_4022765 : Nat := 1377074670056039098091431

theorem tailTrace_4022765 : CollatzResearch.WordTrace tailWord_4022765 prefixEnd_4022765 1377074670056039098091431 := by
  unfold tailWord_4022765
  simp only [CollatzResearch.WordTrace]
  refine ⟨146722293271216913409573749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97814862180811275606382499 146722293271216913409573749)
  ·
    refine ⟨13755214994176585632147539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146722293271216913409573749 13755214994176585632147539)
    ·
      refine ⟨20632822491264878448221309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13755214994176585632147539 20632822491264878448221309)
      ·
        refine ⟨7737308434224329418082991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20632822491264878448221309 7737308434224329418082991)
        ·
          refine ⟨11605962651336494127124487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7737308434224329418082991 11605962651336494127124487)
          ·
            refine ⟨17408943977004741190686731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11605962651336494127124487 17408943977004741190686731)
            ·
              refine ⟨26113415965507111786030097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17408943977004741190686731 26113415965507111786030097)
              ·
                refine ⟨19585061974130333839522573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26113415965507111786030097 19585061974130333839522573)
                ·
                  refine ⟨7344398240298875189820965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19585061974130333839522573 7344398240298875189820965)
                  ·
                    refine ⟨1377074670056039098091431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7344398240298875189820965 1377074670056039098091431)
                    ·
                      rfl

theorem cell22_4022765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4022765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022765 prefixEnd_4022765 := by exact prefixLift 4022765
  have htrace : WordTrace (prefixWord ++ tailWord_4022765) baseStart_4022765 baseEnd_4022765 := by
    simpa [prefixWord, tailWord_4022765, baseEnd_4022765] using wordTrace_append hprefix tailTrace_4022765
  have hstable : (prefixWord ++ tailWord_4022765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022765).length < 2 ^ (prefixWord ++ tailWord_4022765).sum := by decide
  have hdescent : baseEnd_4022765 < baseStart_4022765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022793 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_4022793 : Nat := 118140960795 + 4022793 * 2 ^ 59
def prefixEnd_4022793 : Nat := 4983230072969 + 3 ^ 40 * 4022793 * 2
def baseEnd_4022793 : Nat := 1377084255028256358391345

theorem tailTrace_4022793 : CollatzResearch.WordTrace tailWord_4022793 prefixEnd_4022793 1377084255028256358391345 := by
  unfold tailWord_4022793
  simp only [CollatzResearch.WordTrace]
  refine ⟨146723314515115474191593033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97815543010076982794395355 146723314515115474191593033)
  ·
    refine ⟨110042485886336605643694775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146723314515115474191593033 110042485886336605643694775)
    ·
      refine ⟨165063728829504908465542163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110042485886336605643694775 165063728829504908465542163)
      ·
        refine ⟨247595593244257362698313245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165063728829504908465542163 247595593244257362698313245)
        ·
          refine ⟨92848347466596511011867467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247595593244257362698313245 92848347466596511011867467)
          ·
            refine ⟨139272521199894766517801201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92848347466596511011867467 139272521199894766517801201)
            ·
              refine ⟨104454390899921074888350901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139272521199894766517801201 104454390899921074888350901)
              ·
                refine ⟨9792599146867600770782897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104454390899921074888350901 9792599146867600770782897)
                ·
                  refine ⟨7344449360150700578087173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9792599146867600770782897 7344449360150700578087173)
                  ·
                    refine ⟨1377084255028256358391345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7344449360150700578087173 1377084255028256358391345)
                    ·
                      rfl

theorem cell22_4022793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_4022793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022793 prefixEnd_4022793 := by exact prefixLift 4022793
  have htrace : WordTrace (prefixWord ++ tailWord_4022793) baseStart_4022793 baseEnd_4022793 := by
    simpa [prefixWord, tailWord_4022793, baseEnd_4022793] using wordTrace_append hprefix tailTrace_4022793
  have hstable : (prefixWord ++ tailWord_4022793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022793).length < 2 ^ (prefixWord ++ tailWord_4022793).sum := by decide
  have hdescent : baseEnd_4022793 < baseStart_4022793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022808 : List Nat := [2, 1, 2, 3, 3, 2, 9]
def baseStart_4022808 : Nat := 118140960795 + 4022808 * 2 ^ 59
def prefixEnd_4022808 : Nat := 4983230072969 + 3 ^ 40 * 4022808 * 2
def baseEnd_4022808 : Nat := 51003310734622271083937

theorem tailTrace_4022808 : CollatzResearch.WordTrace tailWord_4022808 prefixEnd_4022808 51003310734622271083937 := by
  unfold tailWord_4022808
  simp only [CollatzResearch.WordTrace]
  refine ⟨73361930805030565876694539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97815907740040754502259385 73361930805030565876694539)
  ·
    refine ⟨110042896207545848815041809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73361930805030565876694539 110042896207545848815041809)
    ·
      refine ⟨82532172155659386611281357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110042896207545848815041809 82532172155659386611281357)
      ·
        refine ⟨30949564558372269979230509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82532172155659386611281357 30949564558372269979230509)
        ·
          refine ⟨11606086709389601242211441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30949564558372269979230509 11606086709389601242211441)
          ·
            refine ⟨8704565032042200931658581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11606086709389601242211441 8704565032042200931658581)
            ·
              refine ⟨51003310734622271083937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8704565032042200931658581 51003310734622271083937)
              ·
                rfl

theorem cell22_4022808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 9].length) (baseStart_4022808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022808 prefixEnd_4022808 := by exact prefixLift 4022808
  have htrace : WordTrace (prefixWord ++ tailWord_4022808) baseStart_4022808 baseEnd_4022808 := by
    simpa [prefixWord, tailWord_4022808, baseEnd_4022808] using wordTrace_append hprefix tailTrace_4022808
  have hstable : (prefixWord ++ tailWord_4022808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022808).length < 2 ^ (prefixWord ++ tailWord_4022808).sum := by decide
  have hdescent : baseEnd_4022808 < baseStart_4022808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022812 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_4022812 : Nat := 118140960795 + 4022812 * 2 ^ 59
def prefixEnd_4022812 : Nat := 4983230072969 + 3 ^ 40 * 4022812 * 2
def baseEnd_4022812 : Nat := 1377090759116546642166287

theorem tailTrace_4022812 : CollatzResearch.WordTrace tailWord_4022812 prefixEnd_4022812 1377090759116546642166287 := by
  unfold tailWord_4022812
  simp only [CollatzResearch.WordTrace]
  refine ⟨73362003751023320218267345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97816005001364426957689793 73362003751023320218267345)
  ·
    refine ⟨55021502813267490163700509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73362003751023320218267345 55021502813267490163700509)
    ·
      refine ⟨20633063554975308811387691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55021502813267490163700509 20633063554975308811387691)
      ·
        refine ⟨30949595332462963217081537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20633063554975308811387691 30949595332462963217081537)
        ·
          refine ⟨23212196499347222412811153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30949595332462963217081537 23212196499347222412811153)
          ·
            refine ⟨17409147374510416809608365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23212196499347222412811153 17409147374510416809608365)
            ·
              refine ⟨6528430265441406303603137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17409147374510416809608365 6528430265441406303603137)
              ·
                refine ⟨4896322699081054727702353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6528430265441406303603137 4896322699081054727702353)
                ·
                  refine ⟨3672242024310791045776765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896322699081054727702353 3672242024310791045776765)
                  ·
                    refine ⟨1377090759116546642166287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672242024310791045776765 1377090759116546642166287)
                    ·
                      rfl

theorem cell22_4022812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_4022812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022812 prefixEnd_4022812 := by exact prefixLift 4022812
  have htrace : WordTrace (prefixWord ++ tailWord_4022812) baseStart_4022812 baseEnd_4022812 := by
    simpa [prefixWord, tailWord_4022812, baseEnd_4022812] using wordTrace_append hprefix tailTrace_4022812
  have hstable : (prefixWord ++ tailWord_4022812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022812).length < 2 ^ (prefixWord ++ tailWord_4022812).sum := by decide
  have hdescent : baseEnd_4022812 < baseStart_4022812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022840 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_4022840 : Nat := 118140960795 + 4022840 * 2 ^ 59
def prefixEnd_4022840 : Nat := 4983230072969 + 3 ^ 40 * 4022840 * 2
def baseEnd_4022840 : Nat := 1377100344088763902466201

theorem tailTrace_4022840 : CollatzResearch.WordTrace tailWord_4022840 prefixEnd_4022840 1377100344088763902466201 := by
  unfold tailWord_4022840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73362514372972600609276987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97816685830630134145702649 73362514372972600609276987)
  ·
    refine ⟨110043771559458900913915481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73362514372972600609276987 110043771559458900913915481)
    ·
      refine ⟨82532828669594175685436611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110043771559458900913915481 82532828669594175685436611)
      ·
        refine ⟨123799243004391263528154917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82532828669594175685436611 123799243004391263528154917)
        ·
          refine ⟨23212358063323361911529047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123799243004391263528154917 23212358063323361911529047)
          ·
            refine ⟨34818537094985042867293571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23212358063323361911529047 34818537094985042867293571)
            ·
              refine ⟨52227805642477564300940357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34818537094985042867293571 52227805642477564300940357)
              ·
                refine ⟨9792713557964543306426317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52227805642477564300940357 9792713557964543306426317)
                ·
                  refine ⟨3672267584236703739909869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9792713557964543306426317 3672267584236703739909869)
                  ·
                    refine ⟨1377100344088763902466201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672267584236703739909869 1377100344088763902466201)
                    ·
                      rfl

theorem cell22_4022840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_4022840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022840 prefixEnd_4022840 := by exact prefixLift 4022840
  have htrace : WordTrace (prefixWord ++ tailWord_4022840) baseStart_4022840 baseEnd_4022840 := by
    simpa [prefixWord, tailWord_4022840, baseEnd_4022840] using wordTrace_append hprefix tailTrace_4022840
  have hstable : (prefixWord ++ tailWord_4022840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022840).length < 2 ^ (prefixWord ++ tailWord_4022840).sum := by decide
  have hdescent : baseEnd_4022840 < baseStart_4022840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022853 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 7]
def baseStart_4022853 : Nat := 118140960795 + 4022853 * 2 ^ 59
def prefixEnd_4022853 : Nat := 4983230072969 + 3 ^ 40 * 4022853 * 2
def baseEnd_4022853 : Nat := 459034931418145400630387

theorem tailTrace_4022853 : CollatzResearch.WordTrace tailWord_4022853 prefixEnd_4022853 459034931418145400630387 := by
  unfold tailWord_4022853
  simp only [CollatzResearch.WordTrace]
  refine ⟨146725502894898104438777213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97817001929932069625851475 146725502894898104438777213)
  ·
    refine ⟨55022063585586789164541455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146725502894898104438777213 55022063585586789164541455)
    ·
      refine ⟨82533095378380183746812183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55022063585586789164541455 82533095378380183746812183)
      ·
        refine ⟨123799643067570275620218275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82533095378380183746812183 123799643067570275620218275)
        ·
          refine ⟨185699464601355413430327413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123799643067570275620218275 185699464601355413430327413)
          ·
            refine ⟨17409324806377070009093195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185699464601355413430327413 17409324806377070009093195)
            ·
              refine ⟨26113987209565605013639793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17409324806377070009093195 26113987209565605013639793)
              ·
                refine ⟨19585490407174203760229845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26113987209565605013639793 19585490407174203760229845)
                ·
                  refine ⟨459034931418145400630387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19585490407174203760229845 459034931418145400630387)
                  ·
                    rfl

theorem cell22_4022853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_4022853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022853 prefixEnd_4022853 := by exact prefixLift 4022853
  have htrace : WordTrace (prefixWord ++ tailWord_4022853) baseStart_4022853 baseEnd_4022853 := by
    simpa [prefixWord, tailWord_4022853, baseEnd_4022853] using wordTrace_append hprefix tailTrace_4022853
  have hstable : (prefixWord ++ tailWord_4022853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022853).length < 2 ^ (prefixWord ++ tailWord_4022853).sum := by decide
  have hdescent : baseEnd_4022853 < baseStart_4022853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022928 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_4022928 : Nat := 118140960795 + 4022928 * 2 ^ 59
def prefixEnd_4022928 : Nat := 4983230072969 + 3 ^ 40 * 4022928 * 2
def baseEnd_4022928 : Nat := 1377130468287161006265931

theorem tailTrace_4022928 : CollatzResearch.WordTrace tailWord_4022928 prefixEnd_4022928 1377130468287161006265931 := by
  unfold tailWord_4022928
  simp only [CollatzResearch.WordTrace]
  refine ⟨73364119184813196123878719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97818825579750928165171625 73364119184813196123878719)
  ·
    refine ⟨110046178777219794185818079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73364119184813196123878719 110046178777219794185818079)
    ·
      refine ⟨165069268165829691278727119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110046178777219794185818079 165069268165829691278727119)
      ·
        refine ⟨247603902248744536918090679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165069268165829691278727119 247603902248744536918090679)
        ·
          refine ⟨371405853373116805377136019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247603902248744536918090679 371405853373116805377136019)
          ·
            refine ⟨557108780059675208065704029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371405853373116805377136019 557108780059675208065704029)
            ·
              refine ⟨208915792522378203024639011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557108780059675208065704029 208915792522378203024639011)
              ·
                refine ⟨313373688783567304536958517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208915792522378203024639011 313373688783567304536958517)
                ·
                  refine ⟨29378783323459434800339861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313373688783567304536958517 29378783323459434800339861)
                  ·
                    refine ⟨1377130468287161006265931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29378783323459434800339861 1377130468287161006265931)
                    ·
                      rfl

theorem cell22_4022928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_4022928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4022928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4022928 prefixEnd_4022928 := by exact prefixLift 4022928
  have htrace : WordTrace (prefixWord ++ tailWord_4022928) baseStart_4022928 baseEnd_4022928 := by
    simpa [prefixWord, tailWord_4022928, baseEnd_4022928] using wordTrace_append hprefix tailTrace_4022928
  have hstable : (prefixWord ++ tailWord_4022928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022928).length < 2 ^ (prefixWord ++ tailWord_4022928).sum := by decide
  have hdescent : baseEnd_4022928 < baseStart_4022928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023026 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_4023026 : Nat := 118140960795 + 4023026 * 2 ^ 59
def prefixEnd_4023026 : Nat := 4983230072969 + 3 ^ 40 * 4023026 * 2
def baseEnd_4023026 : Nat := 1377164015689921417315631

theorem tailTrace_4023026 : CollatzResearch.WordTrace tailWord_4023026 prefixEnd_4023026 1377164015689921417315631 := by
  unfold tailWord_4023026
  simp only [CollatzResearch.WordTrace]
  refine ⟨36682953180817838746206233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97821208482180903323216621 36682953180817838746206233)
  ·
    refine ⟨27512214885613379059654675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36682953180817838746206233 27512214885613379059654675)
    ·
      refine ⟨41268322328420068589482013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27512214885613379059654675 41268322328420068589482013)
      ·
        refine ⟨15475620873157525721055755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41268322328420068589482013 15475620873157525721055755)
        ·
          refine ⟨23213431309736288581583633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15475620873157525721055755 23213431309736288581583633)
          ·
            refine ⟨17410073482302216436187725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23213431309736288581583633 17410073482302216436187725)
            ·
              refine ⟨6528777555863331163570397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17410073482302216436187725 6528777555863331163570397)
              ·
                refine ⟨2448291583448749186338899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6528777555863331163570397 2448291583448749186338899)
                ·
                  refine ⟨3672437375173123779508349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448291583448749186338899 3672437375173123779508349)
                  ·
                    refine ⟨1377164015689921417315631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672437375173123779508349 1377164015689921417315631)
                    ·
                      rfl

theorem cell22_4023026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_4023026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023026 prefixEnd_4023026 := by exact prefixLift 4023026
  have htrace : WordTrace (prefixWord ++ tailWord_4023026) baseStart_4023026 baseEnd_4023026 := by
    simpa [prefixWord, tailWord_4023026, baseEnd_4023026] using wordTrace_append hprefix tailTrace_4023026
  have hstable : (prefixWord ++ tailWord_4023026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023026).length < 2 ^ (prefixWord ++ tailWord_4023026).sum := by decide
  have hdescent : baseEnd_4023026 < baseStart_4023026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023101 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 4]
def baseStart_4023101 : Nat := 118140960795 + 4023101 * 2 ^ 59
def prefixEnd_4023101 : Nat := 4983230072969 + 3 ^ 40 * 4023101 * 2
def baseEnd_4023101 : Nat := 459063229907548740563467

theorem tailTrace_4023101 : CollatzResearch.WordTrace tailWord_4023101 prefixEnd_4023101 459063229907548740563467 := by
  unfold tailWord_4023101
  simp only [CollatzResearch.WordTrace]
  refine ⟨146734548197999642793805157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97823032131999761862536771 146734548197999642793805157)
  ·
    refine ⟨27512727787124933023838467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146734548197999642793805157 27512727787124933023838467)
    ·
      refine ⟨41269091680687399535757701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27512727787124933023838467 41269091680687399535757701)
      ·
        refine ⟨7737954690128887412954569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41269091680687399535757701 7737954690128887412954569)
        ·
          refine ⟨5803466017596665559715927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7737954690128887412954569 5803466017596665559715927)
          ·
            refine ⟨8705199026394998339573891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803466017596665559715927 8705199026394998339573891)
            ·
              refine ⟨13057798539592497509360837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8705199026394998339573891 13057798539592497509360837)
              ·
                refine ⟨2448337226173593283005157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13057798539592497509360837 2448337226173593283005157)
                ·
                  refine ⟨459063229907548740563467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448337226173593283005157 459063229907548740563467)
                  ·
                    rfl

theorem cell22_4023101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_4023101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023101 prefixEnd_4023101 := by exact prefixLift 4023101
  have htrace : WordTrace (prefixWord ++ tailWord_4023101) baseStart_4023101 baseEnd_4023101 := by
    simpa [prefixWord, tailWord_4023101, baseEnd_4023101] using wordTrace_append hprefix tailTrace_4023101
  have hstable : (prefixWord ++ tailWord_4023101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023101).length < 2 ^ (prefixWord ++ tailWord_4023101).sum := by decide
  have hdescent : baseEnd_4023101 < baseStart_4023101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023150 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_4023150 : Nat := 118140960795 + 4023150 * 2 ^ 59
def prefixEnd_4023150 : Nat := 4983230072969 + 3 ^ 40 * 4023150 * 2
def baseEnd_4023150 : Nat := 1377206463424026427215251

theorem tailTrace_4023150 : CollatzResearch.WordTrace tailWord_4023150 prefixEnd_4023150 1377206463424026427215251 := by
  unfold tailWord_4023150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18342041921852765520292363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97824223583214749441559269 18342041921852765520292363)
  ·
    refine ⟨27513062882779148280438545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18342041921852765520292363 27513062882779148280438545)
    ·
      refine ⟨20634797162084361210328909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27513062882779148280438545 20634797162084361210328909)
      ·
        refine ⟨7738048935781635453873341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20634797162084361210328909 7738048935781635453873341)
        ·
          refine ⟨2901768350918113295202503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7738048935781635453873341 2901768350918113295202503)
          ·
            refine ⟨4352652526377169942803755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901768350918113295202503 4352652526377169942803755)
            ·
              refine ⟨6528978789565754914205633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352652526377169942803755 6528978789565754914205633)
              ·
                refine ⟨4896734092174316185654225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6528978789565754914205633 4896734092174316185654225)
                ·
                  refine ⟨3672550569130737139240669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896734092174316185654225 3672550569130737139240669)
                  ·
                    refine ⟨1377206463424026427215251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672550569130737139240669 1377206463424026427215251)
                    ·
                      rfl

theorem cell22_4023150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_4023150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023150 prefixEnd_4023150 := by exact prefixLift 4023150
  have htrace : WordTrace (prefixWord ++ tailWord_4023150) baseStart_4023150 baseEnd_4023150 := by
    simpa [prefixWord, tailWord_4023150, baseEnd_4023150] using wordTrace_append hprefix tailTrace_4023150
  have hstable : (prefixWord ++ tailWord_4023150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023150).length < 2 ^ (prefixWord ++ tailWord_4023150).sum := by decide
  have hdescent : baseEnd_4023150 < baseStart_4023150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023161 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 1, 3]
def baseStart_4023161 : Nat := 118140960795 + 4023161 * 2 ^ 59
def prefixEnd_4023161 : Nat := 4983230072969 + 3 ^ 40 * 4023161 * 2
def baseEnd_4023161 : Nat := 1377210228948826065190217

theorem tailTrace_4023161 : CollatzResearch.WordTrace tailWord_4023161 prefixEnd_4023161 1377210228948826065190217 := by
  unfold tailWord_4023161
  simp only [CollatzResearch.WordTrace]
  refine ⟨146736736577782273040989337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97824491051854848693992891 146736736577782273040989337)
  ·
    refine ⟨110052552433336704780742003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146736736577782273040989337 110052552433336704780742003)
    ·
      refine ⟨165078828650005057171113005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110052552433336704780742003 165078828650005057171113005)
      ·
        refine ⟨61904560743751896439167377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165078828650005057171113005 61904560743751896439167377)
        ·
          refine ⟨46428420557813922329375533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61904560743751896439167377 46428420557813922329375533)
          ·
            refine ⟨17410657709180220873515825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46428420557813922329375533 17410657709180220873515825)
            ·
              refine ⟨13057993281885165655136869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17410657709180220873515825 13057993281885165655136869)
              ·
                refine ⟨2448373740353468560338163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13057993281885165655136869 2448373740353468560338163)
                ·
                  refine ⟨3672560610530202840507245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448373740353468560338163 3672560610530202840507245)
                  ·
                    refine ⟨1377210228948826065190217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672560610530202840507245 1377210228948826065190217)
                    ·
                      rfl

theorem cell22_4023161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_4023161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023161 prefixEnd_4023161 := by exact prefixLift 4023161
  have htrace : WordTrace (prefixWord ++ tailWord_4023161) baseStart_4023161 baseEnd_4023161 := by
    simpa [prefixWord, tailWord_4023161, baseEnd_4023161] using wordTrace_append hprefix tailTrace_4023161
  have hstable : (prefixWord ++ tailWord_4023161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023161).length < 2 ^ (prefixWord ++ tailWord_4023161).sum := by decide
  have hdescent : baseEnd_4023161 < baseStart_4023161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023204 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_4023204 : Nat := 118140960795 + 4023204 * 2 ^ 59
def prefixEnd_4023204 : Nat := 4983230072969 + 3 ^ 40 * 4023204 * 2
def baseEnd_4023204 : Nat := 1377224948727588286365085

theorem tailTrace_4023204 : CollatzResearch.WordTrace tailWord_4023204 prefixEnd_4023204 1377224948727588286365085 := by
  unfold tailWord_4023204
  simp only [CollatzResearch.WordTrace]
  refine ⟨73369152458313245692402333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97825536611084327589869777 73369152458313245692402333)
  ·
    refine ⟨27513432171867467134650875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73369152458313245692402333 27513432171867467134650875)
    ·
      refine ⟨41270148257801200701976313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27513432171867467134650875 41270148257801200701976313)
      ·
        refine ⟨30952611193350900526482235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41270148257801200701976313 30952611193350900526482235)
        ·
          refine ⟨46428916790026350789723353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30952611193350900526482235 46428916790026350789723353)
          ·
            refine ⟨34821687592519763092292515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46428916790026350789723353 34821687592519763092292515)
            ·
              refine ⟨52232531388779644638438773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34821687592519763092292515 52232531388779644638438773)
              ·
                refine ⟨4896799817698091684853635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52232531388779644638438773 4896799817698091684853635)
                ·
                  refine ⟨7345199726547137527280453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896799817698091684853635 7345199726547137527280453)
                  ·
                    refine ⟨1377224948727588286365085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345199726547137527280453 1377224948727588286365085)
                    ·
                      rfl

theorem cell22_4023204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_4023204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023204 prefixEnd_4023204 := by exact prefixLift 4023204
  have htrace : WordTrace (prefixWord ++ tailWord_4023204) baseStart_4023204 baseEnd_4023204 := by
    simpa [prefixWord, tailWord_4023204, baseEnd_4023204] using wordTrace_append hprefix tailTrace_4023204
  have hstable : (prefixWord ++ tailWord_4023204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023204).length < 2 ^ (prefixWord ++ tailWord_4023204).sum := by decide
  have hdescent : baseEnd_4023204 < baseStart_4023204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023247 : List Nat := [1, 1, 2, 1, 1, 6, 2, 8]
def baseStart_4023247 : Nat := 118140960795 + 4023247 * 2 ^ 59
def prefixEnd_4023247 : Nat := 4983230072969 + 3 ^ 40 * 4023247 * 2
def baseEnd_4023247 : Nat := 153026629834038945282217

theorem tailTrace_4023247 : CollatzResearch.WordTrace tailWord_4023247 prefixEnd_4023247 153026629834038945282217 := by
  unfold tailWord_4023247
  simp only [CollatzResearch.WordTrace]
  refine ⟨146739873255470709728619995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97826582170313806485746663 146739873255470709728619995)
  ·
    refine ⟨220109809883206064592929993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146739873255470709728619995 220109809883206064592929993)
    ·
      refine ⟨165082357412404548444697495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220109809883206064592929993 165082357412404548444697495)
      ·
        refine ⟨247623536118606822667046243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165082357412404548444697495 247623536118606822667046243)
        ·
          refine ⟨371435304177910234000569365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247623536118606822667046243 371435304177910234000569365)
          ·
            refine ⟨17411029883339542218776689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 371435304177910234000569365 17411029883339542218776689)
            ·
              refine ⟨13058272412504656664082517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17411029883339542218776689 13058272412504656664082517)
              ·
                refine ⟨153026629834038945282217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13058272412504656664082517 153026629834038945282217)
                ·
                  rfl

theorem cell22_4023247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 8].length) (baseStart_4023247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023247 prefixEnd_4023247 := by exact prefixLift 4023247
  have htrace : WordTrace (prefixWord ++ tailWord_4023247) baseStart_4023247 baseEnd_4023247 := by
    simpa [prefixWord, tailWord_4023247, baseEnd_4023247] using wordTrace_append hprefix tailTrace_4023247
  have hstable : (prefixWord ++ tailWord_4023247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023247).length < 2 ^ (prefixWord ++ tailWord_4023247).sum := by decide
  have hdescent : baseEnd_4023247 < baseStart_4023247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023249 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_4023249 : Nat := 118140960795 + 4023249 * 2 ^ 59
def prefixEnd_4023249 : Nat := 4983230072969 + 3 ^ 40 * 4023249 * 2
def baseEnd_4023249 : Nat := 1377240353147223168989947

theorem tailTrace_4023249 : CollatzResearch.WordTrace tailWord_4023249 prefixEnd_4023249 1377240353147223168989947 := by
  unfold tailWord_4023249
  simp only [CollatzResearch.WordTrace]
  refine ⟨146739946201463464070192801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97826630800975642713461867 146739946201463464070192801)
  ·
    refine ⟨110054959651097598052644601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146739946201463464070192801 110054959651097598052644601)
    ·
      refine ⟨82541219738323198539483451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110054959651097598052644601 82541219738323198539483451)
      ·
        refine ⟨123811829607484797809225177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82541219738323198539483451 123811829607484797809225177)
        ·
          refine ⟨92858872205613598356918883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123811829607484797809225177 92858872205613598356918883)
          ·
            refine ⟨139288308308420397535378325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92858872205613598356918883 139288308308420397535378325)
            ·
              refine ⟨6529139451957206134470859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139288308308420397535378325 6529139451957206134470859)
              ·
                refine ⟨9793709177935809201706289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529139451957206134470859 9793709177935809201706289)
                ·
                  refine ⟨7345281883451856901279717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9793709177935809201706289 7345281883451856901279717)
                  ·
                    refine ⟨1377240353147223168989947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345281883451856901279717 1377240353147223168989947)
                    ·
                      rfl

theorem cell22_4023249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_4023249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023249 prefixEnd_4023249 := by exact prefixLift 4023249
  have htrace : WordTrace (prefixWord ++ tailWord_4023249) baseStart_4023249 baseEnd_4023249 := by
    simpa [prefixWord, tailWord_4023249, baseEnd_4023249] using wordTrace_append hprefix tailTrace_4023249
  have hstable : (prefixWord ++ tailWord_4023249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023249).length < 2 ^ (prefixWord ++ tailWord_4023249).sum := by decide
  have hdescent : baseEnd_4023249 < baseStart_4023249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023354 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_4023354 : Nat := 118140960795 + 4023354 * 2 ^ 59
def prefixEnd_4023354 : Nat := 4983230072969 + 3 ^ 40 * 4023354 * 2
def baseEnd_4023354 : Nat := 459092098931012631704875

theorem tailTrace_4023354 : CollatzResearch.WordTrace tailWord_4023354 prefixEnd_4023354 459092098931012631704875 := by
  unfold tailWord_4023354
  simp only [CollatzResearch.WordTrace]
  refine ⟨36685943966520766750691279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97829183910722044668510077 36685943966520766750691279)
  ·
    refine ⟨55028915949781150126036919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36685943966520766750691279 55028915949781150126036919)
    ·
      refine ⟨82543373924671725189055379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55028915949781150126036919 82543373924671725189055379)
      ·
        refine ⟨123815060887007587783583069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82543373924671725189055379 123815060887007587783583069)
        ·
          refine ⟨46430647832627845418843651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123815060887007587783583069 46430647832627845418843651)
          ·
            refine ⟨69645971748941768128265477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46430647832627845418843651 69645971748941768128265477)
            ·
              refine ⟨13058619702926581524049777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69645971748941768128265477 13058619702926581524049777)
              ·
                refine ⟨9793964777194936143037333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13058619702926581524049777 9793964777194936143037333)
                ·
                  refine ⟨459092098931012631704875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9793964777194936143037333 459092098931012631704875)
                  ·
                    rfl

theorem cell22_4023354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_4023354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023354 prefixEnd_4023354 := by exact prefixLift 4023354
  have htrace : WordTrace (prefixWord ++ tailWord_4023354) baseStart_4023354 baseEnd_4023354 := by
    simpa [prefixWord, tailWord_4023354, baseEnd_4023354] using wordTrace_append hprefix tailTrace_4023354
  have hstable : (prefixWord ++ tailWord_4023354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023354).length < 2 ^ (prefixWord ++ tailWord_4023354).sum := by decide
  have hdescent : baseEnd_4023354 < baseStart_4023354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023356 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_4023356 : Nat := 118140960795 + 4023356 * 2 ^ 59
def prefixEnd_4023356 : Nat := 4983230072969 + 3 ^ 40 * 4023356 * 2
def baseEnd_4023356 : Nat := 1377276981433910556564619

theorem tailTrace_4023356 : CollatzResearch.WordTrace tailWord_4023356 prefixEnd_4023356 1377276981433910556564619 := by
  unfold tailWord_4023356
  simp only [CollatzResearch.WordTrace]
  refine ⟨73371924406037910672168961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97829232541383880896225281 73371924406037910672168961)
  ·
    refine ⟨55028943304528433004126721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73371924406037910672168961 55028943304528433004126721)
    ·
      refine ⟨41271707478396324753095041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55028943304528433004126721 41271707478396324753095041)
      ·
        refine ⟨30953780608797243564821281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41271707478396324753095041 30953780608797243564821281)
        ·
          refine ⟨23215335456597932673615961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30953780608797243564821281 23215335456597932673615961)
          ·
            refine ⟨17411501592448449505211971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23215335456597932673615961 17411501592448449505211971)
            ·
              refine ⟨26117252388672674257817957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17411501592448449505211971 26117252388672674257817957)
              ·
                refine ⟨4896984822876126423340867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26117252388672674257817957 4896984822876126423340867)
                ·
                  refine ⟨7345477234314189635011301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896984822876126423340867 7345477234314189635011301)
                  ·
                    refine ⟨1377276981433910556564619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345477234314189635011301 1377276981433910556564619)
                    ·
                      rfl

theorem cell22_4023356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_4023356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023356 prefixEnd_4023356 := by exact prefixLift 4023356
  have htrace : WordTrace (prefixWord ++ tailWord_4023356) baseStart_4023356 baseEnd_4023356 := by
    simpa [prefixWord, tailWord_4023356, baseEnd_4023356] using wordTrace_append hprefix tailTrace_4023356
  have hstable : (prefixWord ++ tailWord_4023356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023356).length < 2 ^ (prefixWord ++ tailWord_4023356).sum := by decide
  have hdescent : baseEnd_4023356 < baseStart_4023356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023373 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4023373 : Nat := 118140960795 + 4023373 * 2 ^ 59
def prefixEnd_4023373 : Nat := 4983230072969 + 3 ^ 40 * 4023373 * 2
def baseEnd_4023373 : Nat := 1377282800881328178889567

theorem tailTrace_4023373 : CollatzResearch.WordTrace tailWord_4023373 prefixEnd_4023373 1377282800881328178889567 := by
  unfold tailWord_4023373
  simp only [CollatzResearch.WordTrace]
  refine ⟨146744468853014233247706773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97829645902009488831804515 146744468853014233247706773)
  ·
    refine ⟨6878646977485042183486255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146744468853014233247706773 6878646977485042183486255)
    ·
      refine ⟨10317970466227563275229383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6878646977485042183486255 10317970466227563275229383)
      ·
        refine ⟨15476955699341344912844075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10317970466227563275229383 15476955699341344912844075)
        ·
          refine ⟨23215433549012017369266113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15476955699341344912844075 23215433549012017369266113)
          ·
            refine ⟨17411575161759013026949585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23215433549012017369266113 17411575161759013026949585)
            ·
              refine ⟨13058681371319259770212189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17411575161759013026949585 13058681371319259770212189)
              ·
                refine ⟨4897005514244722413829571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13058681371319259770212189 4897005514244722413829571)
                ·
                  refine ⟨7345508271367083620744357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897005514244722413829571 7345508271367083620744357)
                  ·
                    refine ⟨1377282800881328178889567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345508271367083620744357 1377282800881328178889567)
                    ·
                      rfl

theorem cell22_4023373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4023373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023373 prefixEnd_4023373 := by exact prefixLift 4023373
  have htrace : WordTrace (prefixWord ++ tailWord_4023373) baseStart_4023373 baseEnd_4023373 := by
    simpa [prefixWord, tailWord_4023373, baseEnd_4023373] using wordTrace_append hprefix tailTrace_4023373
  have hstable : (prefixWord ++ tailWord_4023373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023373).length < 2 ^ (prefixWord ++ tailWord_4023373).sum := by decide
  have hdescent : baseEnd_4023373 < baseStart_4023373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023399 : List Nat := [1, 1, 5, 1, 1, 3, 1, 9]
def baseStart_4023399 : Nat := 118140960795 + 4023399 * 2 ^ 59
def prefixEnd_4023399 : Nat := 4983230072969 + 3 ^ 40 * 4023399 * 2
def baseEnd_4023399 : Nat := 153032411245852530859943

theorem tailTrace_4023399 : CollatzResearch.WordTrace tailWord_4023399 prefixEnd_4023399 153032411245852530859943 := by
  unfold tailWord_4023399
  simp only [CollatzResearch.WordTrace]
  refine ⟨146745417150920039688153251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97830278100613359792102167 146745417150920039688153251)
  ·
    refine ⟨220118125726380059532229877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146745417150920039688153251 220118125726380059532229877)
    ·
      refine ⟨20636074286848130581146551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220118125726380059532229877 20636074286848130581146551)
      ·
        refine ⟨30954111430272195871719827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20636074286848130581146551 30954111430272195871719827)
        ·
          refine ⟨46431167145408293807579741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30954111430272195871719827 46431167145408293807579741)
          ·
            refine ⟨17411687679528110177842403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46431167145408293807579741 17411687679528110177842403)
            ·
              refine ⟨26117531519292165266763605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17411687679528110177842403 26117531519292165266763605)
              ·
                refine ⟨153032411245852530859943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26117531519292165266763605 153032411245852530859943)
                ·
                  rfl

theorem cell22_4023399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 9].length) (baseStart_4023399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023399 prefixEnd_4023399 := by exact prefixLift 4023399
  have htrace : WordTrace (prefixWord ++ tailWord_4023399) baseStart_4023399 baseEnd_4023399 := by
    simpa [prefixWord, tailWord_4023399, baseEnd_4023399] using wordTrace_append hprefix tailTrace_4023399
  have hstable : (prefixWord ++ tailWord_4023399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023399).length < 2 ^ (prefixWord ++ tailWord_4023399).sum := by decide
  have hdescent : baseEnd_4023399 < baseStart_4023399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023461 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 5]
def baseStart_4023461 : Nat := 118140960795 + 4023461 * 2 ^ 59
def prefixEnd_4023461 : Nat := 4983230072969 + 3 ^ 40 * 4023461 * 2
def baseEnd_4023461 : Nat := 459104308359908427563099

theorem tailTrace_4023461 : CollatzResearch.WordTrace tailWord_4023461 prefixEnd_4023461 459104308359908427563099 := by
  unfold tailWord_4023461
  simp only [CollatzResearch.WordTrace]
  refine ⟨146747678476695424276910237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97831785651130282851273491 146747678476695424276910237)
  ·
    refine ⟨55030379428760784103841339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146747678476695424276910237 55030379428760784103841339)
    ·
      refine ⟨82545569143141176155762009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55030379428760784103841339 82545569143141176155762009)
      ·
        refine ⟨61909176857355882116821507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82545569143141176155762009 61909176857355882116821507)
        ·
          refine ⟨92863765286033823175232261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61909176857355882116821507 92863765286033823175232261)
          ·
            refine ⟨17411955991131341845356049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92863765286033823175232261 17411955991131341845356049)
            ·
              refine ⟨13058966993348506384017037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17411955991131341845356049 13058966993348506384017037)
              ·
                refine ⟨4897112622505689894006389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13058966993348506384017037 4897112622505689894006389)
                ·
                  refine ⟨459104308359908427563099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4897112622505689894006389 459104308359908427563099)
                  ·
                    rfl

theorem cell22_4023461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_4023461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023461 prefixEnd_4023461 := by exact prefixLift 4023461
  have htrace : WordTrace (prefixWord ++ tailWord_4023461) baseStart_4023461 baseEnd_4023461 := by
    simpa [prefixWord, tailWord_4023461, baseEnd_4023461] using wordTrace_append hprefix tailTrace_4023461
  have hstable : (prefixWord ++ tailWord_4023461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023461).length < 2 ^ (prefixWord ++ tailWord_4023461).sum := by decide
  have hdescent : baseEnd_4023461 < baseStart_4023461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023504 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_4023504 : Nat := 118140960795 + 4023504 * 2 ^ 59
def prefixEnd_4023504 : Nat := 4983230072969 + 3 ^ 40 * 4023504 * 2
def baseEnd_4023504 : Nat := 1377327644858487503864165

theorem tailTrace_4023504 : CollatzResearch.WordTrace tailWord_4023504 prefixEnd_4023504 1377327644858487503864165 := by
  unfold tailWord_4023504
  simp only [CollatzResearch.WordTrace]
  refine ⟨73374623407769821310362783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97832831210359761747150377 73374623407769821310362783)
  ·
    refine ⟨110061935111654731965544175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73374623407769821310362783 110061935111654731965544175)
    ·
      refine ⟨165092902667482097948316263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110061935111654731965544175 165092902667482097948316263)
      ·
        refine ⟨247639354001223146922474395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165092902667482097948316263 247639354001223146922474395)
        ·
          refine ⟨371459031001834720383711593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247639354001223146922474395 371459031001834720383711593)
          ·
            refine ⟨278594273251376040287783695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371459031001834720383711593 278594273251376040287783695)
            ·
              refine ⟨417891409877064060431675543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278594273251376040287783695 417891409877064060431675543)
              ·
                refine ⟨626837114815596090647513315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417891409877064060431675543 626837114815596090647513315)
                ·
                  refine ⟨940255672223394135971269973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626837114815596090647513315 940255672223394135971269973)
                  ·
                    refine ⟨1377327644858487503864165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 940255672223394135971269973 1377327644858487503864165)
                    ·
                      rfl

theorem cell22_4023504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_4023504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023504 prefixEnd_4023504 := by exact prefixLift 4023504
  have htrace : WordTrace (prefixWord ++ tailWord_4023504) baseStart_4023504 baseEnd_4023504 := by
    simpa [prefixWord, tailWord_4023504, baseEnd_4023504] using wordTrace_append hprefix tailTrace_4023504
  have hstable : (prefixWord ++ tailWord_4023504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023504).length < 2 ^ (prefixWord ++ tailWord_4023504).sum := by decide
  have hdescent : baseEnd_4023504 < baseStart_4023504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023525 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_4023525 : Nat := 118140960795 + 4023525 * 2 ^ 59
def prefixEnd_4023525 : Nat := 4983230072969 + 3 ^ 40 * 4023525 * 2
def baseEnd_4023525 : Nat := 1377334833587650449089101

theorem tailTrace_4023525 : CollatzResearch.WordTrace tailWord_4023525 prefixEnd_4023525 1377334833587650449089101 := by
  unfold tailWord_4023525
  simp only [CollatzResearch.WordTrace]
  refine ⟨146750012748463563207240029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97833341832309042138160019 146750012748463563207240029)
  ·
    refine ⟨55031254780673836202715011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146750012748463563207240029 55031254780673836202715011)
    ·
      refine ⟨82546882171010754304072517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55031254780673836202715011 82546882171010754304072517)
      ·
        refine ⟨15477540407064516432013597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82546882171010754304072517 15477540407064516432013597)
        ·
          refine ⟨5804077652649193662005099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15477540407064516432013597 5804077652649193662005099)
          ·
            refine ⟨8706116478973790493007649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804077652649193662005099 8706116478973790493007649)
            ·
              refine ⟨6529587359230342869755737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706116478973790493007649 6529587359230342869755737)
              ·
                refine ⟨4897190519422757152316803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529587359230342869755737 4897190519422757152316803)
                ·
                  refine ⟨7345785779134135728475205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897190519422757152316803 7345785779134135728475205)
                  ·
                    refine ⟨1377334833587650449089101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345785779134135728475205 1377334833587650449089101)
                    ·
                      rfl

theorem cell22_4023525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_4023525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023525 prefixEnd_4023525 := by exact prefixLift 4023525
  have htrace : WordTrace (prefixWord ++ tailWord_4023525) baseStart_4023525 baseEnd_4023525 := by
    simpa [prefixWord, tailWord_4023525, baseEnd_4023525] using wordTrace_append hprefix tailTrace_4023525
  have hstable : (prefixWord ++ tailWord_4023525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023525).length < 2 ^ (prefixWord ++ tailWord_4023525).sum := by decide
  have hdescent : baseEnd_4023525 < baseStart_4023525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023551 : List Nat := [1, 1, 2, 2, 1, 7, 8]
def baseStart_4023551 : Nat := 118140960795 + 4023551 * 2 ^ 59
def prefixEnd_4023551 : Nat := 4983230072969 + 3 ^ 40 * 4023551 * 2
def baseEnd_4023551 : Nat := 51012730885888705479223

theorem tailTrace_4023551 : CollatzResearch.WordTrace tailWord_4023551 prefixEnd_4023551 51012730885888705479223 := by
  unfold tailWord_4023551
  simp only [CollatzResearch.WordTrace]
  refine ⟨146750961046369369647686507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97833974030912913098457671 146750961046369369647686507)
  ·
    refine ⟨220126441569554054471529761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146750961046369369647686507 220126441569554054471529761)
    ·
      refine ⟨165094831177165540853647321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220126441569554054471529761 165094831177165540853647321)
      ·
        refine ⟨123821123382874155640235491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165094831177165540853647321 123821123382874155640235491)
        ·
          refine ⟨185731685074311233460353237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123821123382874155640235491 185731685074311233460353237)
          ·
            refine ⟨4353086368929169534227029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 185731685074311233460353237 4353086368929169534227029)
            ·
              refine ⟨51012730885888705479223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4353086368929169534227029 51012730885888705479223)
              ·
                rfl

theorem cell22_4023551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 8].length) (baseStart_4023551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023551 prefixEnd_4023551 := by exact prefixLift 4023551
  have htrace : WordTrace (prefixWord ++ tailWord_4023551) baseStart_4023551 baseEnd_4023551 := by
    simpa [prefixWord, tailWord_4023551, baseEnd_4023551] using wordTrace_append hprefix tailTrace_4023551
  have hstable : (prefixWord ++ tailWord_4023551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023551).length < 2 ^ (prefixWord ++ tailWord_4023551).sum := by decide
  have hdescent : baseEnd_4023551 < baseStart_4023551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023553 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_4023553 : Nat := 118140960795 + 4023553 * 2 ^ 59
def prefixEnd_4023553 : Nat := 4983230072969 + 3 ^ 40 * 4023553 * 2
def baseEnd_4023553 : Nat := 1377344418559867709389015

theorem tailTrace_4023553 : CollatzResearch.WordTrace tailWord_4023553 prefixEnd_4023553 1377344418559867709389015 := by
  unfold tailWord_4023553
  simp only [CollatzResearch.WordTrace]
  refine ⟨146751033992362123989259313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97834022661574749326172875 146751033992362123989259313)
  ·
    refine ⟨110063275494271592991944485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146751033992362123989259313 110063275494271592991944485)
    ·
      refine ⟨20636864155175923685989591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110063275494271592991944485 20636864155175923685989591)
      ·
        refine ⟨30955296232763885528984387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20636864155175923685989591 30955296232763885528984387)
        ·
          refine ⟨46432944349145828293476581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30955296232763885528984387 46432944349145828293476581)
          ·
            refine ⟨8706177065464842805026859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46432944349145828293476581 8706177065464842805026859)
            ·
              refine ⟨13059265598197264207540289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706177065464842805026859 13059265598197264207540289)
              ·
                refine ⟨9794449198647948155655217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13059265598197264207540289 9794449198647948155655217)
                ·
                  refine ⟨7345836898985961116741413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794449198647948155655217 7345836898985961116741413)
                  ·
                    refine ⟨1377344418559867709389015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345836898985961116741413 1377344418559867709389015)
                    ·
                      rfl

theorem cell22_4023553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_4023553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023553 prefixEnd_4023553 := by exact prefixLift 4023553
  have htrace : WordTrace (prefixWord ++ tailWord_4023553) baseStart_4023553 baseEnd_4023553 := by
    simpa [prefixWord, tailWord_4023553, baseEnd_4023553] using wordTrace_append hprefix tailTrace_4023553
  have hstable : (prefixWord ++ tailWord_4023553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023553).length < 2 ^ (prefixWord ++ tailWord_4023553).sum := by decide
  have hdescent : baseEnd_4023553 < baseStart_4023553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023600 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 1, 3]
def baseStart_4023600 : Nat := 118140960795 + 4023600 * 2 ^ 59
def prefixEnd_4023600 : Nat := 4983230072969 + 3 ^ 40 * 4023600 * 2
def baseEnd_4023600 : Nat := 1377360507620375253463871

theorem tailTrace_4023600 : CollatzResearch.WordTrace tailWord_4023600 prefixEnd_4023600 1377360507620375253463871 := by
  unfold tailWord_4023600
  simp only [CollatzResearch.WordTrace]
  refine ⟨73376374111595925508110127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97835165482127900677480169 73376374111595925508110127)
  ·
    refine ⟨110064561167393888262165191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73376374111595925508110127 110064561167393888262165191)
    ·
      refine ⟨165096841751090832393247787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110064561167393888262165191 165096841751090832393247787)
      ·
        refine ⟨247645262626636248589871681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165096841751090832393247787 247645262626636248589871681)
        ·
          refine ⟨185733946969977186442403761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247645262626636248589871681 185733946969977186442403761)
          ·
            refine ⟨139300460227482889831802821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185733946969977186442403761 139300460227482889831802821)
            ·
              refine ⟨26118836292653041843463029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139300460227482889831802821 26118836292653041843463029)
              ·
                refine ⟨2448640902436222672824659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26118836292653041843463029 2448640902436222672824659)
                ·
                  refine ⟨3672961353654334009236989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448640902436222672824659 3672961353654334009236989)
                  ·
                    refine ⟨1377360507620375253463871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672961353654334009236989 1377360507620375253463871)
                    ·
                      rfl

theorem cell22_4023600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_4023600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023600 prefixEnd_4023600 := by exact prefixLift 4023600
  have htrace : WordTrace (prefixWord ++ tailWord_4023600) baseStart_4023600 baseEnd_4023600 := by
    simpa [prefixWord, tailWord_4023600, baseEnd_4023600] using wordTrace_append hprefix tailTrace_4023600
  have hstable : (prefixWord ++ tailWord_4023600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023600).length < 2 ^ (prefixWord ++ tailWord_4023600).sum := by decide
  have hdescent : baseEnd_4023600 < baseStart_4023600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023628 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_4023628 : Nat := 118140960795 + 4023628 * 2 ^ 59
def prefixEnd_4023628 : Nat := 4983230072969 + 3 ^ 40 * 4023628 * 2
def baseEnd_4023628 : Nat := 1377370092592592513763785

theorem tailTrace_4023628 : CollatzResearch.WordTrace tailWord_4023628 prefixEnd_4023628 1377370092592592513763785 := by
  unfold tailWord_4023628
  simp only [CollatzResearch.WordTrace]
  refine ⟨73376884733545205899119769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97835846311393607865493025 73376884733545205899119769)
  ·
    refine ⟨55032663550158904424339827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73376884733545205899119769 55032663550158904424339827)
    ·
      refine ⟨82548995325238356636509741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55032663550158904424339827 82548995325238356636509741)
      ·
        refine ⟨30955873246964383738691153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82548995325238356636509741 30955873246964383738691153)
        ·
          refine ⟨23216904935223287804018365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30955873246964383738691153 23216904935223287804018365)
          ·
            refine ⟨8706339350708732926506887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23216904935223287804018365 8706339350708732926506887)
            ·
              refine ⟨13059509026063099389760331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706339350708732926506887 13059509026063099389760331)
              ·
                refine ⟨19589263539094649084640497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13059509026063099389760331 19589263539094649084640497)
                ·
                  refine ⟨14691947654320986813480373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19589263539094649084640497 14691947654320986813480373)
                  ·
                    refine ⟨1377370092592592513763785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14691947654320986813480373 1377370092592592513763785)
                    ·
                      rfl

theorem cell22_4023628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_4023628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023628 prefixEnd_4023628 := by exact prefixLift 4023628
  have htrace : WordTrace (prefixWord ++ tailWord_4023628) baseStart_4023628 baseEnd_4023628 := by
    simpa [prefixWord, tailWord_4023628, baseEnd_4023628] using wordTrace_append hprefix tailTrace_4023628
  have hstable : (prefixWord ++ tailWord_4023628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023628).length < 2 ^ (prefixWord ++ tailWord_4023628).sum := by decide
  have hdescent : baseEnd_4023628 < baseStart_4023628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023638 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4023638 : Nat := 118140960795 + 4023638 * 2 ^ 59
def prefixEnd_4023638 : Nat := 4983230072969 + 3 ^ 40 * 4023638 * 2
def baseEnd_4023638 : Nat := 1377373515796955821013755

theorem tailTrace_4023638 : CollatzResearch.WordTrace tailWord_4023638 prefixEnd_4023638 1377373515796955821013755 := by
  unfold tailWord_4023638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172133387315886469131473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97836089464702789004069045 9172133387315886469131473)
  ·
    refine ⟨6879100040486914851848605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9172133387315886469131473 6879100040486914851848605)
    ·
      refine ⟨2579662515182593069443227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6879100040486914851848605 2579662515182593069443227)
      ·
        refine ⟨3869493772773889604164841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579662515182593069443227 3869493772773889604164841)
        ·
          refine ⟨2902120329580417203123631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3869493772773889604164841 2902120329580417203123631)
          ·
            refine ⟨4353180494370625804685447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902120329580417203123631 4353180494370625804685447)
            ·
              refine ⟨6529770741555938707028171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353180494370625804685447 6529770741555938707028171)
              ·
                refine ⟨9794656112333908060542257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529770741555938707028171 9794656112333908060542257)
                ·
                  refine ⟨7345992084250431045406693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794656112333908060542257 7345992084250431045406693)
                  ·
                    refine ⟨1377373515796955821013755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345992084250431045406693 1377373515796955821013755)
                    ·
                      rfl

theorem cell22_4023638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4023638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023638 prefixEnd_4023638 := by exact prefixLift 4023638
  have htrace : WordTrace (prefixWord ++ tailWord_4023638) baseStart_4023638 baseEnd_4023638 := by
    simpa [prefixWord, tailWord_4023638, baseEnd_4023638] using wordTrace_append hprefix tailTrace_4023638
  have hstable : (prefixWord ++ tailWord_4023638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023638).length < 2 ^ (prefixWord ++ tailWord_4023638).sum := by decide
  have hdescent : baseEnd_4023638 < baseStart_4023638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023641 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 8]
def baseStart_4023641 : Nat := 118140960795 + 4023641 * 2 ^ 59
def prefixEnd_4023641 : Nat := 4983230072969 + 3 ^ 40 * 4023641 * 2
def baseEnd_4023641 : Nat := 459124847586088271062915

theorem tailTrace_4023641 : CollatzResearch.WordTrace tailWord_4023641 prefixEnd_4023641 459124847586088271062915 := by
  unfold tailWord_4023641
  simp only [CollatzResearch.WordTrace]
  refine ⟨146754243616043315018462777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97836162410695543345641851 146754243616043315018462777)
  ·
    refine ⟨110065682712032486263847083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146754243616043315018462777 110065682712032486263847083)
    ·
      refine ⟨165098524068048729395770625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110065682712032486263847083 165098524068048729395770625)
      ·
        refine ⟨123823893051036547046827969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165098524068048729395770625 123823893051036547046827969)
        ·
          refine ⟨92867919788277410285120977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123823893051036547046827969 92867919788277410285120977)
          ·
            refine ⟨69650939841208057713840733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92867919788277410285120977 69650939841208057713840733)
            ·
              refine ⟨26119102440453021642690275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69650939841208057713840733 26119102440453021642690275)
              ·
                refine ⟨39178653660679532464035413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26119102440453021642690275 39178653660679532464035413)
                ·
                  refine ⟨459124847586088271062915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39178653660679532464035413 459124847586088271062915)
                  ·
                    rfl

theorem cell22_4023641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_4023641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023641 prefixEnd_4023641 := by exact prefixLift 4023641
  have htrace : WordTrace (prefixWord ++ tailWord_4023641) baseStart_4023641 baseEnd_4023641 := by
    simpa [prefixWord, tailWord_4023641, baseEnd_4023641] using wordTrace_append hprefix tailTrace_4023641
  have hstable : (prefixWord ++ tailWord_4023641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023641).length < 2 ^ (prefixWord ++ tailWord_4023641).sum := by decide
  have hdescent : baseEnd_4023641 < baseStart_4023641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023660 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_4023660 : Nat := 118140960795 + 4023660 * 2 ^ 59
def prefixEnd_4023660 : Nat := 4983230072969 + 3 ^ 40 * 4023660 * 2
def baseEnd_4023660 : Nat := 1377381046846555096963687

theorem tailTrace_4023660 : CollatzResearch.WordTrace tailWord_4023660 prefixEnd_4023660 1377381046846555096963687 := by
  unfold tailWord_4023660
  simp only [CollatzResearch.WordTrace]
  refine ⟨73377468301487240631702217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97836624401982987508936289 73377468301487240631702217)
  ·
    refine ⟨55033101226115430473776663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73377468301487240631702217 55033101226115430473776663)
    ·
      refine ⟨82549651839173145710664995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55033101226115430473776663 82549651839173145710664995)
      ·
        refine ⟨123824477758759718565997493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82549651839173145710664995 123824477758759718565997493)
        ·
          refine ⟨11608544789883723615562265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123824477758759718565997493 11608544789883723615562265)
          ·
            refine ⟨8706408592412792711671699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608544789883723615562265 8706408592412792711671699)
            ·
              refine ⟨13059612888619189067507549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706408592412792711671699 13059612888619189067507549)
              ·
                refine ⟨4897354833232195900315331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13059612888619189067507549 4897354833232195900315331)
                ·
                  refine ⟨7346032249848293850472997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897354833232195900315331 7346032249848293850472997)
                  ·
                    refine ⟨1377381046846555096963687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346032249848293850472997 1377381046846555096963687)
                    ·
                      rfl

theorem cell22_4023660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_4023660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023660 prefixEnd_4023660 := by exact prefixLift 4023660
  have htrace : WordTrace (prefixWord ++ tailWord_4023660) baseStart_4023660 baseEnd_4023660 := by
    simpa [prefixWord, tailWord_4023660, baseEnd_4023660] using wordTrace_append hprefix tailTrace_4023660
  have hstable : (prefixWord ++ tailWord_4023660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023660).length < 2 ^ (prefixWord ++ tailWord_4023660).sum := by decide
  have hdescent : baseEnd_4023660 < baseStart_4023660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023688 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4023688 : Nat := 118140960795 + 4023688 * 2 ^ 59
def prefixEnd_4023688 : Nat := 4983230072969 + 3 ^ 40 * 4023688 * 2
def baseEnd_4023688 : Nat := 1377390631818772357263601

theorem tailTrace_4023688 : CollatzResearch.WordTrace tailWord_4023688 prefixEnd_4023688 1377390631818772357263601 := by
  unfold tailWord_4023688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73377978923436521022711859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97837305231248694696949145 73377978923436521022711859)
  ·
    refine ⟨110066968385154781534067789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73377978923436521022711859 110066968385154781534067789)
    ·
      refine ⟨41275113144433043075275421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110066968385154781534067789 41275113144433043075275421)
      ·
        refine ⟨15478167429162391153228283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41275113144433043075275421 15478167429162391153228283)
        ·
          refine ⟨23217251143743586729842425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15478167429162391153228283 23217251143743586729842425)
          ·
            refine ⟨17412938357807690047381819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23217251143743586729842425 17412938357807690047381819)
            ·
              refine ⟨26119407536711535071072729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17412938357807690047381819 26119407536711535071072729)
              ·
                refine ⟨19589555652533651303304547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26119407536711535071072729 19589555652533651303304547)
                ·
                  refine ⟨29384333478800476954956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19589555652533651303304547 29384333478800476954956821)
                  ·
                    refine ⟨1377390631818772357263601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29384333478800476954956821 1377390631818772357263601)
                    ·
                      rfl

theorem cell22_4023688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4023688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023688 prefixEnd_4023688 := by exact prefixLift 4023688
  have htrace : WordTrace (prefixWord ++ tailWord_4023688) baseStart_4023688 baseEnd_4023688 := by
    simpa [prefixWord, tailWord_4023688, baseEnd_4023688] using wordTrace_append hprefix tailTrace_4023688
  have hstable : (prefixWord ++ tailWord_4023688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023688).length < 2 ^ (prefixWord ++ tailWord_4023688).sum := by decide
  have hdescent : baseEnd_4023688 < baseStart_4023688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023797 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4023797 : Nat := 118140960795 + 4023797 * 2 ^ 59
def prefixEnd_4023797 : Nat := 4983230072969 + 3 ^ 40 * 4023797 * 2
def baseEnd_4023797 : Nat := 1377427944746332406288267

theorem tailTrace_4023797 : CollatzResearch.WordTrace tailWord_4023797 prefixEnd_4023797 1377427944746332406288267 := by
  unfold tailWord_4023797
  simp only [CollatzResearch.WordTrace]
  refine ⟨146759933403478153661141645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97839955602318769107427763 146759933403478153661141645)
  ·
    refine ⟨55034975026304307622928117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146759933403478153661141645 55034975026304307622928117)
    ·
      refine ⟨5159528908716028839649511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55034975026304307622928117 5159528908716028839649511)
      ·
        refine ⟨7739293363074043259474267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159528908716028839649511 7739293363074043259474267)
        ·
          refine ⟨11608940044611064889211401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7739293363074043259474267 11608940044611064889211401)
          ·
            refine ⟨8706705033458298666908551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608940044611064889211401 8706705033458298666908551)
            ·
              refine ⟨13060057550187448000362827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706705033458298666908551 13060057550187448000362827)
              ·
                refine ⟨19590086325281172000544241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060057550187448000362827 19590086325281172000544241)
                ·
                  refine ⟨14692564743960879000408181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19590086325281172000544241 14692564743960879000408181)
                  ·
                    refine ⟨1377427944746332406288267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14692564743960879000408181 1377427944746332406288267)
                    ·
                      rfl

theorem cell22_4023797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4023797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023797 prefixEnd_4023797 := by exact prefixLift 4023797
  have htrace : WordTrace (prefixWord ++ tailWord_4023797) baseStart_4023797 baseEnd_4023797 := by
    simpa [prefixWord, tailWord_4023797, baseEnd_4023797] using wordTrace_append hprefix tailTrace_4023797
  have hstable : (prefixWord ++ tailWord_4023797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023797).length < 2 ^ (prefixWord ++ tailWord_4023797).sum := by decide
  have hdescent : baseEnd_4023797 < baseStart_4023797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023825 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_4023825 : Nat := 118140960795 + 4023825 * 2 ^ 59
def prefixEnd_4023825 : Nat := 4983230072969 + 3 ^ 40 * 4023825 * 2
def baseEnd_4023825 : Nat := 1377437529718549666588181

theorem tailTrace_4023825 : CollatzResearch.WordTrace tailWord_4023825 prefixEnd_4023825 1377437529718549666588181 := by
  unfold tailWord_4023825
  simp only [CollatzResearch.WordTrace]
  refine ⟨146760954647376714443160929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97840636431584476295440619 146760954647376714443160929)
  ·
    refine ⟨110070715985532535832370697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146760954647376714443160929 110070715985532535832370697)
    ·
      refine ⟨82553036989149401874278023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110070715985532535832370697 82553036989149401874278023)
      ·
        refine ⟨123829555483724102811417035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82553036989149401874278023 123829555483724102811417035)
        ·
          refine ⟨185744333225586154217125553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123829555483724102811417035 185744333225586154217125553)
          ·
            refine ⟨139308249919189615662844165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185744333225586154217125553 139308249919189615662844165)
            ·
              refine ⟨26120296859848052936783281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139308249919189615662844165 26120296859848052936783281)
              ·
                refine ⟨19590222644886039702587461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26120296859848052936783281 19590222644886039702587461)
                ·
                  refine ⟨3673166745916132444235149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19590222644886039702587461 3673166745916132444235149)
                  ·
                    refine ⟨1377437529718549666588181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673166745916132444235149 1377437529718549666588181)
                    ·
                      rfl

theorem cell22_4023825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_4023825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023825 prefixEnd_4023825 := by exact prefixLift 4023825
  have htrace : WordTrace (prefixWord ++ tailWord_4023825) baseStart_4023825 baseEnd_4023825 := by
    simpa [prefixWord, tailWord_4023825, baseEnd_4023825] using wordTrace_append hprefix tailTrace_4023825
  have hstable : (prefixWord ++ tailWord_4023825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023825).length < 2 ^ (prefixWord ++ tailWord_4023825).sum := by decide
  have hdescent : baseEnd_4023825 < baseStart_4023825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023827 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 4]
def baseStart_4023827 : Nat := 118140960795 + 4023827 * 2 ^ 59
def prefixEnd_4023827 : Nat := 4983230072969 + 3 ^ 40 * 4023827 * 2
def baseEnd_4023827 : Nat := 459146071453140776012725

theorem tailTrace_4023827 : CollatzResearch.WordTrace tailWord_4023827 prefixEnd_4023827 459146071453140776012725 := by
  unfold tailWord_4023827
  simp only [CollatzResearch.WordTrace]
  refine ⟨146761027593369468784733735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97840685062246312523155823 146761027593369468784733735)
  ·
    refine ⟨220141541390054203177100603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146761027593369468784733735 220141541390054203177100603)
    ·
      refine ⟨330212312085081304765650905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220141541390054203177100603 330212312085081304765650905)
      ·
        refine ⟨247659234063810978574238179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330212312085081304765650905 247659234063810978574238179)
        ·
          refine ⟨371488851095716467861357269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247659234063810978574238179 371488851095716467861357269)
          ·
            refine ⟨8706769947555854715500561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 371488851095716467861357269 8706769947555854715500561)
            ·
              refine ⟨6530077460666891036625421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706769947555854715500561 6530077460666891036625421)
              ·
                refine ⟨2448779047750084138734533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6530077460666891036625421 2448779047750084138734533)
                ·
                  refine ⟨459146071453140776012725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448779047750084138734533 459146071453140776012725)
                  ·
                    rfl

theorem cell22_4023827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 4].length) (baseStart_4023827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023827 prefixEnd_4023827 := by exact prefixLift 4023827
  have htrace : WordTrace (prefixWord ++ tailWord_4023827) baseStart_4023827 baseEnd_4023827 := by
    simpa [prefixWord, tailWord_4023827, baseEnd_4023827] using wordTrace_append hprefix tailTrace_4023827
  have hstable : (prefixWord ++ tailWord_4023827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023827).length < 2 ^ (prefixWord ++ tailWord_4023827).sum := by decide
  have hdescent : baseEnd_4023827 < baseStart_4023827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023829 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_4023829 : Nat := 118140960795 + 4023829 * 2 ^ 59
def prefixEnd_4023829 : Nat := 4983230072969 + 3 ^ 40 * 4023829 * 2
def baseEnd_4023829 : Nat := 1377438899000294989488169

theorem tailTrace_4023829 : CollatzResearch.WordTrace tailWord_4023829 prefixEnd_4023829 1377438899000294989488169 := by
  unfold tailWord_4023829
  simp only [CollatzResearch.WordTrace]
  refine ⟨146761100539362223126306541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97840733692908148750871027 146761100539362223126306541)
  ·
    refine ⟨55035412702260833672364953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146761100539362223126306541 55035412702260833672364953)
    ·
      refine ⟨41276559526695625254273715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55035412702260833672364953 41276559526695625254273715)
      ·
        refine ⟨61914839290043437881410573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41276559526695625254273715 61914839290043437881410573)
        ·
          refine ⟨23218064733766289205528965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61914839290043437881410573 23218064733766289205528965)
          ·
            refine ⟨4353387137581179226036681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23218064733766289205528965 4353387137581179226036681)
            ·
              refine ⟨3265040353185884419527511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4353387137581179226036681 3265040353185884419527511)
              ·
                refine ⟨4897560529778826629291267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265040353185884419527511 4897560529778826629291267)
                ·
                  refine ⟨7346340794668239943936901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897560529778826629291267 7346340794668239943936901)
                  ·
                    refine ⟨1377438899000294989488169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346340794668239943936901 1377438899000294989488169)
                    ·
                      rfl

theorem cell22_4023829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_4023829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023829 prefixEnd_4023829 := by exact prefixLift 4023829
  have htrace : WordTrace (prefixWord ++ tailWord_4023829) baseStart_4023829 baseEnd_4023829 := by
    simpa [prefixWord, tailWord_4023829, baseEnd_4023829] using wordTrace_append hprefix tailTrace_4023829
  have hstable : (prefixWord ++ tailWord_4023829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023829).length < 2 ^ (prefixWord ++ tailWord_4023829).sum := by decide
  have hdescent : baseEnd_4023829 < baseStart_4023829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023859 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 2, 3]
def baseStart_4023859 : Nat := 118140960795 + 4023859 * 2 ^ 59
def prefixEnd_4023859 : Nat := 4983230072969 + 3 ^ 40 * 4023859 * 2
def baseEnd_4023859 : Nat := 1377449168613384911238077

theorem tailTrace_4023859 : CollatzResearch.WordTrace tailWord_4023859 prefixEnd_4023859 1377449168613384911238077 := by
  unfold tailWord_4023859
  simp only [CollatzResearch.WordTrace]
  refine ⟨146762194729253538249898631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97841463152835692166599087 146762194729253538249898631)
  ·
    refine ⟨220143292093880307374847947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146762194729253538249898631 220143292093880307374847947)
    ·
      refine ⟨330214938140820461062271921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220143292093880307374847947 330214938140820461062271921)
      ·
        refine ⟨247661203605615345796703941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330214938140820461062271921 247661203605615345796703941)
        ·
          refine ⟨46436475676052877336881989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247661203605615345796703941 46436475676052877336881989)
          ·
            refine ⟨8706839189259914500665373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46436475676052877336881989 8706839189259914500665373)
            ·
              refine ⟨3265064695972467937749515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8706839189259914500665373 3265064695972467937749515)
              ·
                refine ⟨4897597043958701906624273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265064695972467937749515 4897597043958701906624273)
                ·
                  refine ⟨3673197782969026429968205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897597043958701906624273 3673197782969026429968205)
                  ·
                    refine ⟨1377449168613384911238077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673197782969026429968205 1377449168613384911238077)
                    ·
                      rfl

theorem cell22_4023859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 3].length) (baseStart_4023859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023859 prefixEnd_4023859 := by exact prefixLift 4023859
  have htrace : WordTrace (prefixWord ++ tailWord_4023859) baseStart_4023859 baseEnd_4023859 := by
    simpa [prefixWord, tailWord_4023859, baseEnd_4023859] using wordTrace_append hprefix tailTrace_4023859
  have hstable : (prefixWord ++ tailWord_4023859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023859).length < 2 ^ (prefixWord ++ tailWord_4023859).sum := by decide
  have hdescent : baseEnd_4023859 < baseStart_4023859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023878 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_4023878 : Nat := 118140960795 + 4023878 * 2 ^ 59
def prefixEnd_4023878 : Nat := 4983230072969 + 3 ^ 40 * 4023878 * 2
def baseEnd_4023878 : Nat := 459151890900558398337673

theorem tailTrace_4023878 : CollatzResearch.WordTrace tailWord_4023878 prefixEnd_4023878 459151890900558398337673 := by
  unfold tailWord_4023878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586340241130772015463759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97841925144123136329893525 4586340241130772015463759)
  ·
    refine ⟨6879510361696158023195639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586340241130772015463759 6879510361696158023195639)
    ·
      refine ⟨10319265542544237034793459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6879510361696158023195639 10319265542544237034793459)
      ·
        refine ⟨15478898313816355552190189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10319265542544237034793459 15478898313816355552190189)
        ·
          refine ⟨5804586867681133332071321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15478898313816355552190189 5804586867681133332071321)
          ·
            refine ⟨4353440150760849999053491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5804586867681133332071321 4353440150760849999053491)
            ·
              refine ⟨6530160226141274998580237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353440150760849999053491 6530160226141274998580237)
              ·
                refine ⟨2448810084802978124467589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6530160226141274998580237 2448810084802978124467589)
                ·
                  refine ⟨459151890900558398337673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448810084802978124467589 459151890900558398337673)
                  ·
                    rfl

theorem cell22_4023878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_4023878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4023878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4023878 prefixEnd_4023878 := by exact prefixLift 4023878
  have htrace : WordTrace (prefixWord ++ tailWord_4023878) baseStart_4023878 baseEnd_4023878 := by
    simpa [prefixWord, tailWord_4023878, baseEnd_4023878] using wordTrace_append hprefix tailTrace_4023878
  have hstable : (prefixWord ++ tailWord_4023878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023878).length < 2 ^ (prefixWord ++ tailWord_4023878).sum := by decide
  have hdescent : baseEnd_4023878 < baseStart_4023878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024028 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4024028 : Nat := 118140960795 + 4024028 * 2 ^ 59
def prefixEnd_4024028 : Nat := 4983230072969 + 3 ^ 40 * 4024028 * 2
def baseEnd_4024028 : Nat := 1377507020767124803762559

theorem tailTrace_4024028 : CollatzResearch.WordTrace tailWord_4024028 prefixEnd_4024028 1377507020767124803762559 := by
  unfold tailWord_4024028
  simp only [CollatzResearch.WordTrace]
  refine ⟨73384179332820640056400369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97845572443760853408533825 73384179332820640056400369)
  ·
    refine ⟨55038134499615480042300277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73384179332820640056400369 55038134499615480042300277)
    ·
      refine ⟨5159825109338951253965651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55038134499615480042300277 5159825109338951253965651)
      ·
        refine ⟨7739737664008426880948477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159825109338951253965651 7739737664008426880948477)
        ·
          refine ⟨2902401624003160080355679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7739737664008426880948477 2902401624003160080355679)
          ·
            refine ⟨4353602436004740120533519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902401624003160080355679 4353602436004740120533519)
            ·
              refine ⟨6530403654007110180800279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353602436004740120533519 6530403654007110180800279)
              ·
                refine ⟨9795605481010665271200419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6530403654007110180800279 9795605481010665271200419)
                ·
                  refine ⟨14693408221515997906800629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9795605481010665271200419 14693408221515997906800629)
                  ·
                    refine ⟨1377507020767124803762559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14693408221515997906800629 1377507020767124803762559)
                    ·
                      rfl

theorem cell22_4024028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4024028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024028 prefixEnd_4024028 := by exact prefixLift 4024028
  have htrace : WordTrace (prefixWord ++ tailWord_4024028) baseStart_4024028 baseEnd_4024028 := by
    simpa [prefixWord, tailWord_4024028, baseEnd_4024028] using wordTrace_append hprefix tailTrace_4024028
  have hstable : (prefixWord ++ tailWord_4024028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024028).length < 2 ^ (prefixWord ++ tailWord_4024028).sum := by decide
  have hdescent : baseEnd_4024028 < baseStart_4024028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024099 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 1, 4]
def baseStart_4024099 : Nat := 118140960795 + 4024099 * 2 ^ 59
def prefixEnd_4024099 : Nat := 4983230072969 + 3 ^ 40 * 4024099 * 2
def baseEnd_4024099 : Nat := 1377531325518104285237341

theorem tailTrace_4024099 : CollatzResearch.WordTrace tailWord_4024099 prefixEnd_4024099 1377531325518104285237341 := by
  unfold tailWord_4024099
  simp only [CollatzResearch.WordTrace]
  refine ⟨146770948248384059238635351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97847298832256039492423567 146770948248384059238635351)
  ·
    refine ⟨220156422372576088857953027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146770948248384059238635351 220156422372576088857953027)
    ·
      refine ⟨330234633558864133286929541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220156422372576088857953027 330234633558864133286929541)
      ·
        refine ⟨61918993792287024991299289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330234633558864133286929541 61918993792287024991299289)
        ·
          refine ⟨46439245344215268743474467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61918993792287024991299289 46439245344215268743474467)
          ·
            refine ⟨69658868016322903115211701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46439245344215268743474467 69658868016322903115211701)
            ·
              refine ⟨6530518876530272167051097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69658868016322903115211701 6530518876530272167051097)
              ·
                refine ⟨4897889157397704125288323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530518876530272167051097 4897889157397704125288323)
                ·
                  refine ⟨7346833736096556187932485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897889157397704125288323 7346833736096556187932485)
                  ·
                    refine ⟨1377531325518104285237341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346833736096556187932485 1377531325518104285237341)
                    ·
                      rfl

theorem cell22_4024099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 4].length) (baseStart_4024099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024099 prefixEnd_4024099 := by exact prefixLift 4024099
  have htrace : WordTrace (prefixWord ++ tailWord_4024099) baseStart_4024099 baseEnd_4024099 := by
    simpa [prefixWord, tailWord_4024099, baseEnd_4024099] using wordTrace_append hprefix tailTrace_4024099
  have hstable : (prefixWord ++ tailWord_4024099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024099).length < 2 ^ (prefixWord ++ tailWord_4024099).sum := by decide
  have hdescent : baseEnd_4024099 < baseStart_4024099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024131 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 4]
def baseStart_4024131 : Nat := 118140960795 + 4024131 * 2 ^ 59
def prefixEnd_4024131 : Nat := 4983230072969 + 3 ^ 40 * 4024131 * 2
def baseEnd_4024131 : Nat := 459180759924022289479081

theorem tailTrace_4024131 : CollatzResearch.WordTrace tailWord_4024131 prefixEnd_4024131 459180759924022289479081 := by
  unfold tailWord_4024131
  simp only [CollatzResearch.WordTrace]
  refine ⟨146772115384268128703800247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97848076922845419135866831 146772115384268128703800247)
  ·
    refine ⟨220158173076402193055700371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146772115384268128703800247 220158173076402193055700371)
    ·
      refine ⟨330237259614603289583550557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220158173076402193055700371 330237259614603289583550557)
      ·
        refine ⟨123838972355476233593831459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330237259614603289583550557 123838972355476233593831459)
        ·
          refine ⟨185758458533214350390747189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123838972355476233593831459 185758458533214350390747189)
          ·
            refine ⟨17414855487488845349132549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185758458533214350390747189 17414855487488845349132549)
            ·
              refine ⟨3265285403904158502962353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17414855487488845349132549 3265285403904158502962353)
              ·
                refine ⟨2448964052928118877221765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265285403904158502962353 2448964052928118877221765)
                ·
                  refine ⟨459180759924022289479081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448964052928118877221765 459180759924022289479081)
                  ·
                    rfl

theorem cell22_4024131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 4].length) (baseStart_4024131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024131 prefixEnd_4024131 := by exact prefixLift 4024131
  have htrace : WordTrace (prefixWord ++ tailWord_4024131) baseStart_4024131 baseEnd_4024131 := by
    simpa [prefixWord, tailWord_4024131, baseEnd_4024131] using wordTrace_append hprefix tailTrace_4024131
  have hstable : (prefixWord ++ tailWord_4024131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024131).length < 2 ^ (prefixWord ++ tailWord_4024131).sum := by decide
  have hdescent : baseEnd_4024131 < baseStart_4024131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024146 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_4024146 : Nat := 118140960795 + 4024146 * 2 ^ 59
def prefixEnd_4024146 : Nat := 4983230072969 + 3 ^ 40 * 4024146 * 2
def baseEnd_4024146 : Nat := 1377547414578611829312197

theorem tailTrace_4024146 : CollatzResearch.WordTrace tailWord_4024146 prefixEnd_4024146 1377547414578611829312197 := by
  unfold tailWord_4024146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693165619803446566399073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97848441652809190843730861 36693165619803446566399073)
  ·
    refine ⟨27519874214852584924799305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36693165619803446566399073 27519874214852584924799305)
    ·
      refine ⟨20639905661139438693599479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27519874214852584924799305 20639905661139438693599479)
      ·
        refine ⟨30959858491709158040399219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20639905661139438693599479 30959858491709158040399219)
        ·
          refine ⟨46439787737563737060598829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30959858491709158040399219 46439787737563737060598829)
          ·
            refine ⟨17414920401586401397724561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46439787737563737060598829 17414920401586401397724561)
            ·
              refine ⟨13061190301189801048293421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17414920401586401397724561 13061190301189801048293421)
              ·
                refine ⟨4897946362946175393110033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13061190301189801048293421 4897946362946175393110033)
                ·
                  refine ⟨3673459772209631544832525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897946362946175393110033 3673459772209631544832525)
                  ·
                    refine ⟨1377547414578611829312197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673459772209631544832525 1377547414578611829312197)
                    ·
                      rfl

theorem cell22_4024146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_4024146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024146 prefixEnd_4024146 := by exact prefixLift 4024146
  have htrace : WordTrace (prefixWord ++ tailWord_4024146) baseStart_4024146 baseEnd_4024146 := by
    simpa [prefixWord, tailWord_4024146, baseEnd_4024146] using wordTrace_append hprefix tailTrace_4024146
  have hstable : (prefixWord ++ tailWord_4024146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024146).length < 2 ^ (prefixWord ++ tailWord_4024146).sum := by decide
  have hdescent : baseEnd_4024146 < baseStart_4024146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024159 : List Nat := [1, 1, 2, 3, 1, 5, 3, 6]
def baseStart_4024159 : Nat := 118140960795 + 4024159 * 2 ^ 59
def prefixEnd_4024159 : Nat := 4983230072969 + 3 ^ 40 * 4024159 * 2
def baseEnd_4024159 : Nat := 153061318304920458748573

theorem tailTrace_4024159 : CollatzResearch.WordTrace tailWord_4024159 prefixEnd_4024159 153061318304920458748573 := by
  unfold tailWord_4024159
  simp only [CollatzResearch.WordTrace]
  refine ⟨146773136628166689485819531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97848757752111126323879687 146773136628166689485819531)
  ·
    refine ⟨220159704942250034228729297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146773136628166689485819531 220159704942250034228729297)
    ·
      refine ⟨165119778706687525671546973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220159704942250034228729297 165119778706687525671546973)
      ·
        refine ⟨61919917015007822126830115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165119778706687525671546973 61919917015007822126830115)
        ·
          refine ⟨92879875522511733190245173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61919917015007822126830115 92879875522511733190245173)
          ·
            refine ⟨8707488330235474986585485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92879875522511733190245173 8707488330235474986585485)
            ·
              refine ⟨3265308123838303119969557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8707488330235474986585485 3265308123838303119969557)
              ·
                refine ⟨153061318304920458748573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3265308123838303119969557 153061318304920458748573)
                ·
                  rfl

theorem cell22_4024159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 6].length) (baseStart_4024159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024159 prefixEnd_4024159 := by exact prefixLift 4024159
  have htrace : WordTrace (prefixWord ++ tailWord_4024159) baseStart_4024159 baseEnd_4024159 := by
    simpa [prefixWord, tailWord_4024159, baseEnd_4024159] using wordTrace_append hprefix tailTrace_4024159
  have hstable : (prefixWord ++ tailWord_4024159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024159).length < 2 ^ (prefixWord ++ tailWord_4024159).sum := by decide
  have hdescent : baseEnd_4024159 < baseStart_4024159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024268 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_4024268 : Nat := 118140960795 + 4024268 * 2 ^ 59
def prefixEnd_4024268 : Nat := 4983230072969 + 3 ^ 40 * 4024268 * 2
def baseEnd_4024268 : Nat := 1377589177671844177761823

theorem tailTrace_4024268 : CollatzResearch.WordTrace tailWord_4024268 prefixEnd_4024268 1377589177671844177761823 := by
  unfold tailWord_4024268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73388556092385900550768729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97851408123181200734358305 73388556092385900550768729)
  ·
    refine ⟨55041417069289425413076547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73388556092385900550768729 55041417069289425413076547)
    ·
      refine ⟨82562125603934138119614821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55041417069289425413076547 82562125603934138119614821)
      ·
        refine ⟨15480398550737650897427779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82562125603934138119614821 15480398550737650897427779)
        ·
          refine ⟨23220597826106476346141669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15480398550737650897427779 23220597826106476346141669)
          ·
            refine ⟨4353862092394964314901563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23220597826106476346141669 4353862092394964314901563)
            ·
              refine ⟨6530793138592446472352345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353862092394964314901563 6530793138592446472352345)
              ·
                refine ⟨4898094853944334854264259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530793138592446472352345 4898094853944334854264259)
                ·
                  refine ⟨7347142280916502281396389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898094853944334854264259 7347142280916502281396389)
                  ·
                    refine ⟨1377589177671844177761823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347142280916502281396389 1377589177671844177761823)
                    ·
                      rfl

theorem cell22_4024268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_4024268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024268 prefixEnd_4024268 := by exact prefixLift 4024268
  have htrace : WordTrace (prefixWord ++ tailWord_4024268) baseStart_4024268 baseEnd_4024268 := by
    simpa [prefixWord, tailWord_4024268, baseEnd_4024268] using wordTrace_append hprefix tailTrace_4024268
  have hstable : (prefixWord ++ tailWord_4024268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024268).length < 2 ^ (prefixWord ++ tailWord_4024268).sum := by decide
  have hdescent : baseEnd_4024268 < baseStart_4024268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024281 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_4024281 : Nat := 118140960795 + 4024281 * 2 ^ 59
def prefixEnd_4024281 : Nat := 4983230072969 + 3 ^ 40 * 4024281 * 2
def baseEnd_4024281 : Nat := 1377593627837516477186783

theorem tailTrace_4024281 : CollatzResearch.WordTrace tailWord_4024281 prefixEnd_4024281 1377593627837516477186783 := by
  unfold tailWord_4024281
  simp only [CollatzResearch.WordTrace]
  refine ⟨146777586333724704321760697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97851724222483136214507131 146777586333724704321760697)
  ·
    refine ⟨110083189750293528241320523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146777586333724704321760697 110083189750293528241320523)
    ·
      refine ⟨165124784625440292361980785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110083189750293528241320523 165124784625440292361980785)
      ·
        refine ⟨123843588469080219271485589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165124784625440292361980785 123843588469080219271485589)
        ·
          refine ⟨5805168209488135278350887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123843588469080219271485589 5805168209488135278350887)
          ·
            refine ⟨8707752314232202917526331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805168209488135278350887 8707752314232202917526331)
            ·
              refine ⟨13061628471348304376289497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707752314232202917526331 13061628471348304376289497)
              ·
                refine ⟨9796221353511228282217123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13061628471348304376289497 9796221353511228282217123)
                ·
                  refine ⟨14694332030266842423325685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9796221353511228282217123 14694332030266842423325685)
                  ·
                    refine ⟨1377593627837516477186783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14694332030266842423325685 1377593627837516477186783)
                    ·
                      rfl

theorem cell22_4024281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_4024281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024281 prefixEnd_4024281 := by exact prefixLift 4024281
  have htrace : WordTrace (prefixWord ++ tailWord_4024281) baseStart_4024281 baseEnd_4024281 := by
    simpa [prefixWord, tailWord_4024281, baseEnd_4024281] using wordTrace_append hprefix tailTrace_4024281
  have hstable : (prefixWord ++ tailWord_4024281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024281).length < 2 ^ (prefixWord ++ tailWord_4024281).sum := by decide
  have hdescent : baseEnd_4024281 < baseStart_4024281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024285 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_4024285 : Nat := 118140960795 + 4024285 * 2 ^ 59
def prefixEnd_4024285 : Nat := 4983230072969 + 3 ^ 40 * 4024285 * 2
def baseEnd_4024285 : Nat := 1377594997119261800086771

theorem tailTrace_4024285 : CollatzResearch.WordTrace tailWord_4024285 prefixEnd_4024285 1377594997119261800086771 := by
  unfold tailWord_4024285
  simp only [CollatzResearch.WordTrace]
  refine ⟨146777732225710213004906309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97851821483806808669937539 146777732225710213004906309)
  ·
    refine ⟨27520824792320664938419933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146777732225710213004906309 27520824792320664938419933)
    ·
      refine ⟨10320309297120249351907475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27520824792320664938419933 10320309297120249351907475)
      ·
        refine ⟨15480463945680374027861213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10320309297120249351907475 15480463945680374027861213)
        ·
          refine ⟨5805173979630140260447955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15480463945680374027861213 5805173979630140260447955)
          ·
            refine ⟨8707760969445210390671933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805173979630140260447955 8707760969445210390671933)
            ·
              refine ⟨3265410363541953896501975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8707760969445210390671933 3265410363541953896501975)
              ·
                refine ⟨4898115545312930844752963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265410363541953896501975 4898115545312930844752963)
                ·
                  refine ⟨7347173317969396267129445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898115545312930844752963 7347173317969396267129445)
                  ·
                    refine ⟨1377594997119261800086771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347173317969396267129445 1377594997119261800086771)
                    ·
                      rfl

theorem cell22_4024285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_4024285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024285 prefixEnd_4024285 := by exact prefixLift 4024285
  have htrace : WordTrace (prefixWord ++ tailWord_4024285) baseStart_4024285 baseEnd_4024285 := by
    simpa [prefixWord, tailWord_4024285, baseEnd_4024285] using wordTrace_append hprefix tailTrace_4024285
  have hstable : (prefixWord ++ tailWord_4024285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024285).length < 2 ^ (prefixWord ++ tailWord_4024285).sum := by decide
  have hdescent : baseEnd_4024285 < baseStart_4024285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024298 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4024298 : Nat := 118140960795 + 4024298 * 2 ^ 59
def prefixEnd_4024298 : Nat := 4983230072969 + 3 ^ 40 * 4024298 * 2
def baseEnd_4024298 : Nat := 1377599447284934099511731

theorem tailTrace_4024298 : CollatzResearch.WordTrace tailWord_4024298 prefixEnd_4024298 1377599447284934099511731 := by
  unfold tailWord_4024298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36694551593665779056282387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97852137583108744150086365 36694551593665779056282387)
  ·
    refine ⟨55041827390498668584423581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36694551593665779056282387 55041827390498668584423581)
    ·
      refine ⟨20640685271437000719158843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55041827390498668584423581 20640685271437000719158843)
      ·
        refine ⟨30961027907155501078738265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20640685271437000719158843 30961027907155501078738265)
        ·
          refine ⟨23220770930366625809053699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30961027907155501078738265 23220770930366625809053699)
          ·
            refine ⟨34831156395549938713580549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23220770930366625809053699 34831156395549938713580549)
            ·
              refine ⟨6530841824165613508796353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34831156395549938713580549 6530841824165613508796353)
              ·
                refine ⟨4898131368124210131597265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6530841824165613508796353 4898131368124210131597265)
                ·
                  refine ⟨3673598526093157598697949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4898131368124210131597265 3673598526093157598697949)
                  ·
                    refine ⟨1377599447284934099511731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673598526093157598697949 1377599447284934099511731)
                    ·
                      rfl

theorem cell22_4024298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4024298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024298 prefixEnd_4024298 := by exact prefixLift 4024298
  have htrace : WordTrace (prefixWord ++ tailWord_4024298) baseStart_4024298 baseEnd_4024298 := by
    simpa [prefixWord, tailWord_4024298, baseEnd_4024298] using wordTrace_append hprefix tailTrace_4024298
  have hstable : (prefixWord ++ tailWord_4024298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024298).length < 2 ^ (prefixWord ++ tailWord_4024298).sum := by decide
  have hdescent : baseEnd_4024298 < baseStart_4024298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024330 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_4024330 : Nat := 118140960795 + 4024330 * 2 ^ 59
def prefixEnd_4024330 : Nat := 4983230072969 + 3 ^ 40 * 4024330 * 2
def baseEnd_4024330 : Nat := 1377610401538896682711633

theorem tailTrace_4024330 : CollatzResearch.WordTrace tailWord_4024330 prefixEnd_4024330 1377610401538896682711633 := by
  unfold tailWord_4024330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36694843377636796422573611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97852915673698123793529629 36694843377636796422573611)
  ·
    refine ⟨55042265066455194633860417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36694843377636796422573611 55042265066455194633860417)
    ·
      refine ⟨41281698799841395975395313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55042265066455194633860417 41281698799841395975395313)
      ·
        refine ⟨30961274099881046981546485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41281698799841395975395313 30961274099881046981546485)
        ·
          refine ⟨2902619446863848154519983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30961274099881046981546485 2902619446863848154519983)
          ·
            refine ⟨4353929170295772231779975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902619446863848154519983 4353929170295772231779975)
            ·
              refine ⟨6530893755443658347669963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353929170295772231779975 6530893755443658347669963)
              ·
                refine ⟨9796340633165487521504945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6530893755443658347669963 9796340633165487521504945)
                ·
                  refine ⟨7347255474874115641128709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9796340633165487521504945 7347255474874115641128709)
                  ·
                    refine ⟨1377610401538896682711633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347255474874115641128709 1377610401538896682711633)
                    ·
                      rfl

theorem cell22_4024330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_4024330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024330 prefixEnd_4024330 := by exact prefixLift 4024330
  have htrace : WordTrace (prefixWord ++ tailWord_4024330) baseStart_4024330 baseEnd_4024330 := by
    simpa [prefixWord, tailWord_4024330, baseEnd_4024330] using wordTrace_append hprefix tailTrace_4024330
  have hstable : (prefixWord ++ tailWord_4024330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024330).length < 2 ^ (prefixWord ++ tailWord_4024330).sum := by decide
  have hdescent : baseEnd_4024330 < baseStart_4024330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024433 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_4024433 : Nat := 118140960795 + 4024433 * 2 ^ 59
def prefixEnd_4024433 : Nat := 4983230072969 + 3 ^ 40 * 4024433 * 2
def baseEnd_4024433 : Nat := 1377645660543838747386317

theorem tailTrace_4024433 : CollatzResearch.WordTrace tailWord_4024433 prefixEnd_4024433 1377645660543838747386317 := by
  unfold tailWord_4024433
  simp only [CollatzResearch.WordTrace]
  refine ⟨146783130229174034281293953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97855420152782689520862635 146783130229174034281293953)
  ·
    refine ⟨110087347671880525710970465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146783130229174034281293953 110087347671880525710970465)
    ·
      refine ⟨82565510753910394283227849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110087347671880525710970465 82565510753910394283227849)
      ·
        refine ⟨61924133065432795712420887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82565510753910394283227849 61924133065432795712420887)
        ·
          refine ⟨92886199598149193568631331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61924133065432795712420887 92886199598149193568631331)
          ·
            refine ⟨139329299397223790352946997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92886199598149193568631331 139329299397223790352946997)
            ·
              refine ⟨13062121818489730345588781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139329299397223790352946997 13062121818489730345588781)
              ·
                refine ⟨4898295681933648879595793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13062121818489730345588781 4898295681933648879595793)
                ·
                  refine ⟨3673721761450236659696845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4898295681933648879595793 3673721761450236659696845)
                  ·
                    refine ⟨1377645660543838747386317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673721761450236659696845 1377645660543838747386317)
                    ·
                      rfl

theorem cell22_4024433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_4024433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024433 prefixEnd_4024433 := by exact prefixLift 4024433
  have htrace : WordTrace (prefixWord ++ tailWord_4024433) baseStart_4024433 baseEnd_4024433 := by
    simpa [prefixWord, tailWord_4024433, baseEnd_4024433] using wordTrace_append hprefix tailTrace_4024433
  have hstable : (prefixWord ++ tailWord_4024433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024433).length < 2 ^ (prefixWord ++ tailWord_4024433).sum := by decide
  have hdescent : baseEnd_4024433 < baseStart_4024433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024476 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_4024476 : Nat := 118140960795 + 4024476 * 2 ^ 59
def prefixEnd_4024476 : Nat := 4983230072969 + 3 ^ 40 * 4024476 * 2
def baseEnd_4024476 : Nat := 1377660380322600968561185

theorem tailTrace_4024476 : CollatzResearch.WordTrace tailWord_4024476 prefixEnd_4024476 1377660380322600968561185 := by
  unfold tailWord_4024476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73392349284009126312554641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97856465712012168416739521 73392349284009126312554641)
  ·
    refine ⟨55044261963006844734415981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73392349284009126312554641 55044261963006844734415981)
    ·
      refine ⟨20641598236127566775405993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55044261963006844734415981 20641598236127566775405993)
      ·
        refine ⟨15481198677095675081554495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20641598236127566775405993 15481198677095675081554495)
        ·
          refine ⟨23221798015643512622331743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15481198677095675081554495 23221798015643512622331743)
          ·
            refine ⟨34832697023465268933497615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23221798015643512622331743 34832697023465268933497615)
            ·
              refine ⟨52249045535197903400246423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34832697023465268933497615 52249045535197903400246423)
              ·
                refine ⟨78373568302796855100369635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52249045535197903400246423 78373568302796855100369635)
                ·
                  refine ⟨117560352454195282650554453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78373568302796855100369635 117560352454195282650554453)
                  ·
                    refine ⟨1377660380322600968561185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117560352454195282650554453 1377660380322600968561185)
                    ·
                      rfl

theorem cell22_4024476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_4024476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024476 prefixEnd_4024476 := by exact prefixLift 4024476
  have htrace : WordTrace (prefixWord ++ tailWord_4024476) baseStart_4024476 baseEnd_4024476 := by
    simpa [prefixWord, tailWord_4024476, baseEnd_4024476] using wordTrace_append hprefix tailTrace_4024476
  have hstable : (prefixWord ++ tailWord_4024476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024476).length < 2 ^ (prefixWord ++ tailWord_4024476).sum := by decide
  have hdescent : baseEnd_4024476 < baseStart_4024476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024512 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 1, 3]
def baseStart_4024512 : Nat := 118140960795 + 4024512 * 2 ^ 59
def prefixEnd_4024512 : Nat := 4983230072969 + 3 ^ 40 * 4024512 * 2
def baseEnd_4024512 : Nat := 1377672703858308874661075

theorem tailTrace_4024512 : CollatzResearch.WordTrace tailWord_4024512 prefixEnd_4024512 1377672703858308874661075 := by
  unfold tailWord_4024512
  simp only [CollatzResearch.WordTrace]
  refine ⟨73393005797943915386709895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97857341063925220515613193 73393005797943915386709895)
  ·
    refine ⟨110089508696915873080064843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73393005797943915386709895 110089508696915873080064843)
    ·
      refine ⟨165134263045373809620097265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110089508696915873080064843 165134263045373809620097265)
      ·
        refine ⟨123850697284030357215072949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165134263045373809620097265 123850697284030357215072949)
        ·
          refine ⟨11611002870377845988913089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123850697284030357215072949 11611002870377845988913089)
          ·
            refine ⟨8708252152783384491684817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11611002870377845988913089 8708252152783384491684817)
            ·
              refine ⟨6531189114587538368763613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708252152783384491684817 6531189114587538368763613)
              ·
                refine ⟨2449195917970326888286355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6531189114587538368763613 2449195917970326888286355)
                ·
                  refine ⟨3673793876955490332429533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449195917970326888286355 3673793876955490332429533)
                  ·
                    refine ⟨1377672703858308874661075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673793876955490332429533 1377672703858308874661075)
                    ·
                      rfl

theorem cell22_4024512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_4024512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024512 prefixEnd_4024512 := by exact prefixLift 4024512
  have htrace : WordTrace (prefixWord ++ tailWord_4024512) baseStart_4024512 baseEnd_4024512 := by
    simpa [prefixWord, tailWord_4024512, baseEnd_4024512] using wordTrace_append hprefix tailTrace_4024512
  have hstable : (prefixWord ++ tailWord_4024512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024512).length < 2 ^ (prefixWord ++ tailWord_4024512).sum := by decide
  have hdescent : baseEnd_4024512 < baseStart_4024512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_4024521 : Nat := 118140960795 + 4024521 * 2 ^ 59
def prefixEnd_4024521 : Nat := 4983230072969 + 3 ^ 40 * 4024521 * 2
def baseEnd_4024521 : Nat := 1377675784742235851186047

theorem tailTrace_4024521 : CollatzResearch.WordTrace tailWord_4024521 prefixEnd_4024521 1377675784742235851186047 := by
  unfold tailWord_4024521
  simp only [CollatzResearch.WordTrace]
  refine ⟨146786339852855225310497417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97857559901903483540331611 146786339852855225310497417)
  ·
    refine ⟨110089754889641418982873063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146786339852855225310497417 110089754889641418982873063)
    ·
      refine ⟨165134632334462128474309595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110089754889641418982873063 165134632334462128474309595)
      ·
        refine ⟨247701948501693192711464393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165134632334462128474309595 247701948501693192711464393)
        ·
          refine ⟨185776461376269894533598295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247701948501693192711464393 185776461376269894533598295)
          ·
            refine ⟨278664692064404841800397443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185776461376269894533598295 278664692064404841800397443)
            ·
              refine ⟨417997038096607262700596165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278664692064404841800397443 417997038096607262700596165)
              ·
                refine ⟨78374444643113861756361781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417997038096607262700596165 78374444643113861756361781)
                ·
                  refine ⟨7347604185291924539658917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78374444643113861756361781 7347604185291924539658917)
                  ·
                    refine ⟨1377675784742235851186047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347604185291924539658917 1377675784742235851186047)
                    ·
                      rfl

theorem cell22_4024521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_4024521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024521 prefixEnd_4024521 := by exact prefixLift 4024521
  have htrace : WordTrace (prefixWord ++ tailWord_4024521) baseStart_4024521 baseEnd_4024521 := by
    simpa [prefixWord, tailWord_4024521, baseEnd_4024521] using wordTrace_append hprefix tailTrace_4024521
  have hstable : (prefixWord ++ tailWord_4024521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024521).length < 2 ^ (prefixWord ++ tailWord_4024521).sum := by decide
  have hdescent : baseEnd_4024521 < baseStart_4024521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024570 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_4024570 : Nat := 118140960795 + 4024570 * 2 ^ 59
def prefixEnd_4024570 : Nat := 4983230072969 + 3 ^ 40 * 4024570 * 2
def baseEnd_4024570 : Nat := 459230852814538685570299

theorem tailTrace_4024570 : CollatzResearch.WordTrace tailWord_4024570 prefixEnd_4024570 459230852814538685570299 := by
  unfold tailWord_4024570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36697031757419426669757791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97858751353118471119354109 36697031757419426669757791)
  ·
    refine ⟨55045547636129140004636687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36697031757419426669757791 55045547636129140004636687)
    ·
      refine ⟨82568321454193710006955031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55045547636129140004636687 82568321454193710006955031)
      ·
        refine ⟨123852482181290565010432547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82568321454193710006955031 123852482181290565010432547)
        ·
          refine ⟨185778723271935847515648821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123852482181290565010432547 185778723271935847515648821)
          ·
            refine ⟨17416755306743985704592077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185778723271935847515648821 17416755306743985704592077)
            ·
              refine ⟨6531283240028994639222029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17416755306743985704592077 6531283240028994639222029)
              ·
                refine ⟨2449231215010872989708261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6531283240028994639222029 2449231215010872989708261)
                ·
                  refine ⟨459230852814538685570299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449231215010872989708261 459230852814538685570299)
                  ·
                    rfl

theorem cell22_4024570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_4024570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024570 prefixEnd_4024570 := by exact prefixLift 4024570
  have htrace : WordTrace (prefixWord ++ tailWord_4024570) baseStart_4024570 baseEnd_4024570 := by
    simpa [prefixWord, tailWord_4024570, baseEnd_4024570] using wordTrace_append hprefix tailTrace_4024570
  have hstable : (prefixWord ++ tailWord_4024570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024570).length < 2 ^ (prefixWord ++ tailWord_4024570).sum := by decide
  have hdescent : baseEnd_4024570 < baseStart_4024570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024602 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_4024602 : Nat := 118140960795 + 4024602 * 2 ^ 59
def prefixEnd_4024602 : Nat := 4983230072969 + 3 ^ 40 * 4024602 * 2
def baseEnd_4024602 : Nat := 1377703512697578639910799

theorem tailTrace_4024602 : CollatzResearch.WordTrace tailWord_4024602 prefixEnd_4024602 1377703512697578639910799 := by
  unfold tailWord_4024602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36697323541390444036049015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97859529443707850762797373 36697323541390444036049015)
  ·
    refine ⟨55045985312085666054073523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36697323541390444036049015 55045985312085666054073523)
    ·
      refine ⟨82568977968128499081110285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55045985312085666054073523 82568977968128499081110285)
      ·
        refine ⟨30963366738048187155416357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82568977968128499081110285 30963366738048187155416357)
        ·
          refine ⟨5805631263384035091640567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30963366738048187155416357 5805631263384035091640567)
          ·
            refine ⟨8708446895076052637460851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805631263384035091640567 8708446895076052637460851)
            ·
              refine ⟨13062670342614078956191277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708446895076052637460851 13062670342614078956191277)
              ·
                refine ⟨4898501378480279608571729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13062670342614078956191277 4898501378480279608571729)
                ·
                  refine ⟨3673876033860209706428797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4898501378480279608571729 3673876033860209706428797)
                  ·
                    refine ⟨1377703512697578639910799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673876033860209706428797 1377703512697578639910799)
                    ·
                      rfl

theorem cell22_4024602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_4024602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024602 prefixEnd_4024602 := by exact prefixLift 4024602
  have htrace : WordTrace (prefixWord ++ tailWord_4024602) baseStart_4024602 baseEnd_4024602 := by
    simpa [prefixWord, tailWord_4024602, baseEnd_4024602] using wordTrace_append hprefix tailTrace_4024602
  have hstable : (prefixWord ++ tailWord_4024602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024602).length < 2 ^ (prefixWord ++ tailWord_4024602).sum := by decide
  have hdescent : baseEnd_4024602 < baseStart_4024602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024643 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 5]
def baseStart_4024643 : Nat := 118140960795 + 4024643 * 2 ^ 59
def prefixEnd_4024643 : Nat := 4983230072969 + 3 ^ 40 * 4024643 * 2
def baseEnd_4024643 : Nat := 459239182611822733211891

theorem tailTrace_4024643 : CollatzResearch.WordTrace tailWord_4024643 prefixEnd_4024643 459239182611822733211891 := by
  unfold tailWord_4024643
  simp only [CollatzResearch.WordTrace]
  refine ⟨146790789558413240146438583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97860526372275493430959055 146790789558413240146438583)
  ·
    refine ⟨220186184337619860219657875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146790789558413240146438583 220186184337619860219657875)
    ·
      refine ⟨330279276506429790329486813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220186184337619860219657875 330279276506429790329486813)
      ·
        refine ⟨123854728689911171373557555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330279276506429790329486813 123854728689911171373557555)
        ·
          refine ⟨185782093034866757060336333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123854728689911171373557555 185782093034866757060336333)
          ·
            refine ⟨69668284888075033897626125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185782093034866757060336333 69668284888075033897626125)
            ·
              refine ⟨26125606833028137711609797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69668284888075033897626125 26125606833028137711609797)
              ·
                refine ⟨4898551281192775820926837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26125606833028137711609797 4898551281192775820926837)
                ·
                  refine ⟨459239182611822733211891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4898551281192775820926837 459239182611822733211891)
                  ·
                    rfl

theorem cell22_4024643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 5].length) (baseStart_4024643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024643 prefixEnd_4024643 := by exact prefixLift 4024643
  have htrace : WordTrace (prefixWord ++ tailWord_4024643) baseStart_4024643 baseEnd_4024643 := by
    simpa [prefixWord, tailWord_4024643, baseEnd_4024643] using wordTrace_append hprefix tailTrace_4024643
  have hstable : (prefixWord ++ tailWord_4024643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024643).length < 2 ^ (prefixWord ++ tailWord_4024643).sum := by decide
  have hdescent : baseEnd_4024643 < baseStart_4024643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024647 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 1, 3]
def baseStart_4024647 : Nat := 118140960795 + 4024647 * 2 ^ 59
def prefixEnd_4024647 : Nat := 4983230072969 + 3 ^ 40 * 4024647 * 2
def baseEnd_4024647 : Nat := 1377718917117213522535661

theorem tailTrace_4024647 : CollatzResearch.WordTrace tailWord_4024647 prefixEnd_4024647 1377718917117213522535661 := by
  unfold tailWord_4024647
  simp only [CollatzResearch.WordTrace]
  refine ⟨146790935450398748829584195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97860623633599165886389463 146790935450398748829584195)
  ·
    refine ⟨220186403175598123244376293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146790935450398748829584195 220186403175598123244376293)
    ·
      refine ⟨41284950595424648108320555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220186403175598123244376293 41284950595424648108320555)
      ·
        refine ⟨61927425893136972162480833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41284950595424648108320555 61927425893136972162480833)
        ·
          refine ⟨46445569419852729121860625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61927425893136972162480833 46445569419852729121860625)
          ·
            refine ⟨34834177064889546841395469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46445569419852729121860625 34834177064889546841395469)
            ·
              refine ⟨13062816399333580065523301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34834177064889546841395469 13062816399333580065523301)
              ·
                refine ⟨2449278074875046262285619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13062816399333580065523301 2449278074875046262285619)
                ·
                  refine ⟨3673917112312569393428429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449278074875046262285619 3673917112312569393428429)
                  ·
                    refine ⟨1377718917117213522535661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673917112312569393428429 1377718917117213522535661)
                    ·
                      rfl

theorem cell22_4024647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_4024647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024647 prefixEnd_4024647 := by exact prefixLift 4024647
  have htrace : WordTrace (prefixWord ++ tailWord_4024647) baseStart_4024647 baseEnd_4024647 := by
    simpa [prefixWord, tailWord_4024647, baseEnd_4024647] using wordTrace_append hprefix tailTrace_4024647
  have hstable : (prefixWord ++ tailWord_4024647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024647).length < 2 ^ (prefixWord ++ tailWord_4024647).sum := by decide
  have hdescent : baseEnd_4024647 < baseStart_4024647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024658 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_4024658 : Nat := 118140960795 + 4024658 * 2 ^ 59
def prefixEnd_4024658 : Nat := 4983230072969 + 3 ^ 40 * 4024658 * 2
def baseEnd_4024658 : Nat := 1377722682642013160510627

theorem tailTrace_4024658 : CollatzResearch.WordTrace tailWord_4024658 prefixEnd_4024658 1377722682642013160510627 := by
  unfold tailWord_4024658
  simp only [CollatzResearch.WordTrace]
  refine ⟨36697834163339724427058657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97860891102239265138823085 36697834163339724427058657)
  ·
    refine ⟨27523375622504793320293993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36697834163339724427058657 27523375622504793320293993)
    ·
      refine ⟨20642531716878594990220495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27523375622504793320293993 20642531716878594990220495)
      ·
        refine ⟨30963797575317892485330743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20642531716878594990220495 30963797575317892485330743)
        ·
          refine ⟨46445696362976838727996115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30963797575317892485330743 46445696362976838727996115)
          ·
            refine ⟨69668544544465258091994173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46445696362976838727996115 69668544544465258091994173)
            ·
              refine ⟨26125704204174471784497815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69668544544465258091994173 26125704204174471784497815)
              ·
                refine ⟨39188556306261707676746723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26125704204174471784497815 39188556306261707676746723)
                ·
                  refine ⟨58782834459392561515120085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39188556306261707676746723 58782834459392561515120085)
                  ·
                    refine ⟨1377722682642013160510627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58782834459392561515120085 1377722682642013160510627)
                    ·
                      rfl

theorem cell22_4024658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_4024658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024658 prefixEnd_4024658 := by exact prefixLift 4024658
  have htrace : WordTrace (prefixWord ++ tailWord_4024658) baseStart_4024658 baseEnd_4024658 := by
    simpa [prefixWord, tailWord_4024658, baseEnd_4024658] using wordTrace_append hprefix tailTrace_4024658
  have hstable : (prefixWord ++ tailWord_4024658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024658).length < 2 ^ (prefixWord ++ tailWord_4024658).sum := by decide
  have hdescent : baseEnd_4024658 < baseStart_4024658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024660 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4024660 : Nat := 118140960795 + 4024660 * 2 ^ 59
def prefixEnd_4024660 : Nat := 4983230072969 + 3 ^ 40 * 4024660 * 2
def baseEnd_4024660 : Nat := 459241122427628607320207

theorem tailTrace_4024660 : CollatzResearch.WordTrace tailWord_4024660 prefixEnd_4024660 459241122427628607320207 := by
  unfold tailWord_4024660
  simp only [CollatzResearch.WordTrace]
  refine ⟨73395704799675826024903717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97860939732901101366538289 73395704799675826024903717)
  ·
    refine ⟨13761694649939217379669447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73395704799675826024903717 13761694649939217379669447)
    ·
      refine ⟨20642541974908826069504171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13761694649939217379669447 20642541974908826069504171)
      ·
        refine ⟨30963812962363239104256257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20642541974908826069504171 30963812962363239104256257)
        ·
          refine ⟨23222859721772429328192193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30963812962363239104256257 23222859721772429328192193)
          ·
            refine ⟨17417144791329321996144145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23222859721772429328192193 17417144791329321996144145)
            ·
              refine ⟨13062858593496991497108109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17417144791329321996144145 13062858593496991497108109)
              ·
                refine ⟨4898571972561371811415541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13062858593496991497108109 4898571972561371811415541)
                ·
                  refine ⟨459241122427628607320207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4898571972561371811415541 459241122427628607320207)
                  ·
                    rfl

theorem cell22_4024660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4024660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024660 prefixEnd_4024660 := by exact prefixLift 4024660
  have htrace : WordTrace (prefixWord ++ tailWord_4024660) baseStart_4024660 baseEnd_4024660 := by
    simpa [prefixWord, tailWord_4024660, baseEnd_4024660] using wordTrace_append hprefix tailTrace_4024660
  have hstable : (prefixWord ++ tailWord_4024660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024660).length < 2 ^ (prefixWord ++ tailWord_4024660).sum := by decide
  have hdescent : baseEnd_4024660 < baseStart_4024660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024705 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 6]
def baseStart_4024705 : Nat := 118140960795 + 4024705 * 2 ^ 59
def prefixEnd_4024705 : Nat := 4983230072969 + 3 ^ 40 * 4024705 * 2
def baseEnd_4024705 : Nat := 459246257234173568195161

theorem tailTrace_4024705 : CollatzResearch.WordTrace tailWord_4024705 prefixEnd_4024705 459246257234173568195161 := by
  unfold tailWord_4024705
  simp only [CollatzResearch.WordTrace]
  refine ⟨146793050884188624735195569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97862033922792416490130379 146793050884188624735195569)
  ·
    refine ⟨110094788163141468551396677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146793050884188624735195569 110094788163141468551396677)
    ·
      refine ⟨20642772780589025353386877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110094788163141468551396677 20642772780589025353386877)
      ·
        refine ⟨7741039792720884507520079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20642772780589025353386877 7741039792720884507520079)
        ·
          refine ⟨11611559689081326761280119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7741039792720884507520079 11611559689081326761280119)
          ·
            refine ⟨17417339533621990141920179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11611559689081326761280119 17417339533621990141920179)
            ·
              refine ⟨26126009300432985212880269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17417339533621990141920179 26126009300432985212880269)
              ·
                refine ⟨9797253487662369454830101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26126009300432985212880269 9797253487662369454830101)
                ·
                  refine ⟨459246257234173568195161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9797253487662369454830101 459246257234173568195161)
                  ·
                    rfl

theorem cell22_4024705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_4024705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024705 prefixEnd_4024705 := by exact prefixLift 4024705
  have htrace : WordTrace (prefixWord ++ tailWord_4024705) baseStart_4024705 baseEnd_4024705 := by
    simpa [prefixWord, tailWord_4024705, baseEnd_4024705] using wordTrace_append hprefix tailTrace_4024705
  have hstable : (prefixWord ++ tailWord_4024705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024705).length < 2 ^ (prefixWord ++ tailWord_4024705).sum := by decide
  have hdescent : baseEnd_4024705 < baseStart_4024705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024724 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4024724 : Nat := 118140960795 + 4024724 * 2 ^ 59
def prefixEnd_4024724 : Nat := 4983230072969 + 3 ^ 40 * 4024724 * 2
def baseEnd_4024724 : Nat := 1377745275790810988360425

theorem tailTrace_4024724 : CollatzResearch.WordTrace tailWord_4024724 prefixEnd_4024724 1377745275790810988360425 := by
  unfold tailWord_4024724
  simp only [CollatzResearch.WordTrace]
  refine ⟨73396871935559895490068613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97862495914079860653424817 73396871935559895490068613)
  ·
    refine ⟨13761913487917480404387865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73396871935559895490068613 13761913487917480404387865)
    ·
      refine ⟨10321435115938110303290899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13761913487917480404387865 10321435115938110303290899)
      ·
        refine ⟨15482152673907165454936349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10321435115938110303290899 15482152673907165454936349)
        ·
          refine ⟨5805807252715187045601131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15482152673907165454936349 5805807252715187045601131)
          ·
            refine ⟨8708710879072780568401697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805807252715187045601131 8708710879072780568401697)
            ·
              refine ⟨6531533159304585426301273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708710879072780568401697 6531533159304585426301273)
              ·
                refine ⟨4898649869478439069725955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6531533159304585426301273 4898649869478439069725955)
                ·
                  refine ⟨7347974804217658604588933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898649869478439069725955 7347974804217658604588933)
                  ·
                    refine ⟨1377745275790810988360425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347974804217658604588933 1377745275790810988360425)
                    ·
                      rfl

theorem cell22_4024724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4024724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024724 prefixEnd_4024724 := by exact prefixLift 4024724
  have htrace : WordTrace (prefixWord ++ tailWord_4024724) baseStart_4024724 baseEnd_4024724 := by
    simpa [prefixWord, tailWord_4024724, baseEnd_4024724] using wordTrace_append hprefix tailTrace_4024724
  have hstable : (prefixWord ++ tailWord_4024724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024724).length < 2 ^ (prefixWord ++ tailWord_4024724).sum := by decide
  have hdescent : baseEnd_4024724 < baseStart_4024724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024735 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 2, 4]
def baseStart_4024735 : Nat := 118140960795 + 4024735 * 2 ^ 59
def prefixEnd_4024735 : Nat := 4983230072969 + 3 ^ 40 * 4024735 * 2
def baseEnd_4024735 : Nat := 1377749041315610626335391

theorem tailTrace_4024735 : CollatzResearch.WordTrace tailWord_4024735 prefixEnd_4024735 1377749041315610626335391 := by
  unfold tailWord_4024735
  simp only [CollatzResearch.WordTrace]
  refine ⟨146794145074079939858787659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97862763382719959905858439 146794145074079939858787659)
  ·
    refine ⟨220191217611119909788181489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146794145074079939858787659 220191217611119909788181489)
    ·
      refine ⟨165143413208339932341136117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220191217611119909788181489 165143413208339932341136117)
      ·
        refine ⟨15482194988281868656981511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165143413208339932341136117 15482194988281868656981511)
        ·
          refine ⟨23223292482422802985472267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482194988281868656981511 23223292482422802985472267)
          ·
            refine ⟨34834938723634204478208401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23223292482422802985472267 34834938723634204478208401)
            ·
              refine ⟨26126204042725653358656301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34834938723634204478208401 26126204042725653358656301)
              ·
                refine ⟨9797326516022120009496113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26126204042725653358656301 9797326516022120009496113)
                ·
                  refine ⟨7347994887016590007122085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797326516022120009496113 7347994887016590007122085)
                  ·
                    refine ⟨1377749041315610626335391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347994887016590007122085 1377749041315610626335391)
                    ·
                      rfl

theorem cell22_4024735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_4024735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024735 prefixEnd_4024735 := by exact prefixLift 4024735
  have htrace : WordTrace (prefixWord ++ tailWord_4024735) baseStart_4024735 baseEnd_4024735 := by
    simpa [prefixWord, tailWord_4024735, baseEnd_4024735] using wordTrace_append hprefix tailTrace_4024735
  have hstable : (prefixWord ++ tailWord_4024735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024735).length < 2 ^ (prefixWord ++ tailWord_4024735).sum := by decide
  have hdescent : baseEnd_4024735 < baseStart_4024735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024756 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4024756 : Nat := 118140960795 + 4024756 * 2 ^ 59
def prefixEnd_4024756 : Nat := 4983230072969 + 3 ^ 40 * 4024756 * 2
def baseEnd_4024756 : Nat := 459252076681591190520109

theorem tailTrace_4024756 : CollatzResearch.WordTrace tailWord_4024756 prefixEnd_4024756 459252076681591190520109 := by
  unfold tailWord_4024756
  simp only [CollatzResearch.WordTrace]
  refine ⟨73397455503501930222651061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97863274004669240296868081 73397455503501930222651061)
  ·
    refine ⟨6881011453453305958373537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73397455503501930222651061 6881011453453305958373537)
    ·
      refine ⟨5160758590089979468780153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6881011453453305958373537 5160758590089979468780153)
      ·
        refine ⟨3870568942567484601585115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5160758590089979468780153 3870568942567484601585115)
        ·
          refine ⟨5805853413851226902377673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870568942567484601585115 5805853413851226902377673)
          ·
            refine ⟨4354390060388420176783255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5805853413851226902377673 4354390060388420176783255)
            ·
              refine ⟨6531585090582630265174883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354390060388420176783255 6531585090582630265174883)
              ·
                refine ⟨9797377635873945397762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531585090582630265174883 9797377635873945397762325)
                ·
                  refine ⟨459252076681591190520109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9797377635873945397762325 459252076681591190520109)
                  ·
                    rfl

theorem cell22_4024756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4024756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024756 prefixEnd_4024756 := by exact prefixLift 4024756
  have htrace : WordTrace (prefixWord ++ tailWord_4024756) baseStart_4024756 baseEnd_4024756 := by
    simpa [prefixWord, tailWord_4024756, baseEnd_4024756] using wordTrace_append hprefix tailTrace_4024756
  have hstable : (prefixWord ++ tailWord_4024756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024756).length < 2 ^ (prefixWord ++ tailWord_4024756).sum := by decide
  have hdescent : baseEnd_4024756 < baseStart_4024756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024825 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_4024825 : Nat := 118140960795 + 4024825 * 2 ^ 59
def prefixEnd_4024825 : Nat := 4983230072969 + 3 ^ 40 * 4024825 * 2
def baseEnd_4024825 : Nat := 1377779850154880391585115

theorem tailTrace_4024825 : CollatzResearch.WordTrace tailWord_4024825 prefixEnd_4024825 1377779850154880391585115 := by
  unfold tailWord_4024825
  simp only [CollatzResearch.WordTrace]
  refine ⟨146797427643753885229563929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97864951762502590153042619 146797427643753885229563929)
  ·
    refine ⟨110098070732815413922172947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146797427643753885229563929 110098070732815413922172947)
    ·
      refine ⟨165147106099223120883259421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110098070732815413922172947 165147106099223120883259421)
      ·
        refine ⟨61930164787208670331222283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165147106099223120883259421 61930164787208670331222283)
        ·
          refine ⟨92895247180813005496833425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61930164787208670331222283 92895247180813005496833425)
          ·
            refine ⟨69671435385609754122625069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92895247180813005496833425 69671435385609754122625069)
            ·
              refine ⟨26126788269603657795984401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69671435385609754122625069 26126788269603657795984401)
              ·
                refine ⟨19595091202202743346988301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26126788269603657795984401 19595091202202743346988301)
                ·
                  refine ⟨7348159200826028755120613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19595091202202743346988301 7348159200826028755120613)
                  ·
                    refine ⟨1377779850154880391585115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348159200826028755120613 1377779850154880391585115)
                    ·
                      rfl

theorem cell22_4024825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_4024825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024825 prefixEnd_4024825 := by exact prefixLift 4024825
  have htrace : WordTrace (prefixWord ++ tailWord_4024825) baseStart_4024825 baseEnd_4024825 := by
    simpa [prefixWord, tailWord_4024825, baseEnd_4024825] using wordTrace_append hprefix tailTrace_4024825
  have hstable : (prefixWord ++ tailWord_4024825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024825).length < 2 ^ (prefixWord ++ tailWord_4024825).sum := by decide
  have hdescent : baseEnd_4024825 < baseStart_4024825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024842 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_4024842 : Nat := 118140960795 + 4024842 * 2 ^ 59
def prefixEnd_4024842 : Nat := 4983230072969 + 3 ^ 40 * 4024842 * 2
def baseEnd_4024842 : Nat := 1377785669602298013910063

theorem tailTrace_4024842 : CollatzResearch.WordTrace tailWord_4024842 prefixEnd_4024842 1377785669602298013910063 := by
  unfold tailWord_4024842
  simp only [CollatzResearch.WordTrace]
  refine ⟨36699511921173074283233195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97865365123128198088621853 36699511921173074283233195)
  ·
    refine ⟨55049267881759611424849793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36699511921173074283233195 55049267881759611424849793)
    ·
      refine ⟨41286950911319708568637345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55049267881759611424849793 41286950911319708568637345)
      ·
        refine ⟨30965213183489781426478009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41286950911319708568637345 30965213183489781426478009)
        ·
          refine ⟨23223909887617336069858507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30965213183489781426478009 23223909887617336069858507)
          ·
            refine ⟨34835864831426004104787761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23223909887617336069858507 34835864831426004104787761)
            ·
              refine ⟨26126898623569503078590821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34835864831426004104787761 26126898623569503078590821)
              ·
                refine ⟨4898793491919281827235779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26126898623569503078590821 4898793491919281827235779)
                ·
                  refine ⟨7348190237878922740853669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898793491919281827235779 7348190237878922740853669)
                  ·
                    refine ⟨1377785669602298013910063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348190237878922740853669 1377785669602298013910063)
                    ·
                      rfl

theorem cell22_4024842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_4024842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024842 prefixEnd_4024842 := by exact prefixLift 4024842
  have htrace : WordTrace (prefixWord ++ tailWord_4024842) baseStart_4024842 baseEnd_4024842 := by
    simpa [prefixWord, tailWord_4024842, baseEnd_4024842] using wordTrace_append hprefix tailTrace_4024842
  have hstable : (prefixWord ++ tailWord_4024842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024842).length < 2 ^ (prefixWord ++ tailWord_4024842).sum := by decide
  have hdescent : baseEnd_4024842 < baseStart_4024842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024874 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_4024874 : Nat := 118140960795 + 4024874 * 2 ^ 59
def prefixEnd_4024874 : Nat := 4983230072969 + 3 ^ 40 * 4024874 * 2
def baseEnd_4024874 : Nat := 459265541285420199036655

theorem tailTrace_4024874 : CollatzResearch.WordTrace tailWord_4024874 prefixEnd_4024874 459265541285420199036655 := by
  unfold tailWord_4024874
  simp only [CollatzResearch.WordTrace]
  refine ⟨36699803705144091649524419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97866143213717577732065117 36699803705144091649524419)
  ·
    refine ⟨55049705557716137474286629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36699803705144091649524419 55049705557716137474286629)
    ·
      refine ⟨10321819792071775776428743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55049705557716137474286629 10321819792071775776428743)
      ·
        refine ⟨15482729688107663664643115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10321819792071775776428743 15482729688107663664643115)
        ·
          refine ⟨23224094532161495496964673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482729688107663664643115 23224094532161495496964673)
          ·
            refine ⟨17418070899121121622723505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23224094532161495496964673 17418070899121121622723505)
            ·
              refine ⟨13063553174340841217042629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17418070899121121622723505 13063553174340841217042629)
              ·
                refine ⟨2449416220188907728195493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13063553174340841217042629 2449416220188907728195493)
                ·
                  refine ⟨459265541285420199036655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449416220188907728195493 459265541285420199036655)
                  ·
                    rfl

theorem cell22_4024874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_4024874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024874 prefixEnd_4024874 := by exact prefixLift 4024874
  have htrace : WordTrace (prefixWord ++ tailWord_4024874) baseStart_4024874 baseEnd_4024874 := by
    simpa [prefixWord, tailWord_4024874, baseEnd_4024874] using wordTrace_append hprefix tailTrace_4024874
  have hstable : (prefixWord ++ tailWord_4024874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024874).length < 2 ^ (prefixWord ++ tailWord_4024874).sum := by decide
  have hdescent : baseEnd_4024874 < baseStart_4024874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024885 : List Nat := [1, 3, 3, 1, 1, 2, 2, 9]
def baseStart_4024885 : Nat := 118140960795 + 4024885 * 2 ^ 59
def prefixEnd_4024885 : Nat := 4983230072969 + 3 ^ 40 * 4024885 * 2
def baseEnd_4024885 : Nat := 153088932153451137231659

theorem tailTrace_4024885 : CollatzResearch.WordTrace tailWord_4024885 prefixEnd_4024885 153088932153451137231659 := by
  unfold tailWord_4024885
  simp only [CollatzResearch.WordTrace]
  refine ⟨146799616023536515476748109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97866410682357676984498739 146799616023536515476748109)
  ·
    refine ⟨55049856008826193303780541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146799616023536515476748109 55049856008826193303780541)
    ·
      refine ⟨20643696003309822488917703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55049856008826193303780541 20643696003309822488917703)
      ·
        refine ⟨30965544004964733733376555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20643696003309822488917703 30965544004964733733376555)
        ·
          refine ⟨46448316007447100600064833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30965544004964733733376555 46448316007447100600064833)
          ·
            refine ⟨34836237005585325450048625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46448316007447100600064833 34836237005585325450048625)
            ·
              refine ⟨26127177754188994087536469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34836237005585325450048625 26127177754188994087536469)
              ·
                refine ⟨153088932153451137231659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26127177754188994087536469 153088932153451137231659)
                ·
                  rfl

theorem cell22_4024885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 9].length) (baseStart_4024885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024885 prefixEnd_4024885 := by exact prefixLift 4024885
  have htrace : WordTrace (prefixWord ++ tailWord_4024885) baseStart_4024885 baseEnd_4024885 := by
    simpa [prefixWord, tailWord_4024885, baseEnd_4024885] using wordTrace_append hprefix tailTrace_4024885
  have hstable : (prefixWord ++ tailWord_4024885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024885).length < 2 ^ (prefixWord ++ tailWord_4024885).sum := by decide
  have hdescent : baseEnd_4024885 < baseStart_4024885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024917 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_4024917 : Nat := 118140960795 + 4024917 * 2 ^ 59
def prefixEnd_4024917 : Nat := 4983230072969 + 3 ^ 40 * 4024917 * 2
def baseEnd_4024917 : Nat := 1377811343635022818284833

theorem tailTrace_4024917 : CollatzResearch.WordTrace tailWord_4024917 prefixEnd_4024917 1377811343635022818284833 := by
  unfold tailWord_4024917
  simp only [CollatzResearch.WordTrace]
  refine ⟨146800783159420584941913005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97867188772947056627942003 146800783159420584941913005)
  ·
    refine ⟨55050293684782719353217377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146800783159420584941913005 55050293684782719353217377)
    ·
      refine ⟨41287720263587039514913033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55050293684782719353217377 41287720263587039514913033)
      ·
        refine ⟨30965790197690279636184775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41287720263587039514913033 30965790197690279636184775)
        ·
          refine ⟨46448685296535419454277163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30965790197690279636184775 46448685296535419454277163)
          ·
            refine ⟨69673027944803129181415745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46448685296535419454277163 69673027944803129181415745)
            ·
              refine ⟨52254770958602346886061809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69673027944803129181415745 52254770958602346886061809)
              ·
                refine ⟨39191078218951760164546357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52254770958602346886061809 39191078218951760164546357)
                ·
                  refine ⟨3674163583026727515426221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39191078218951760164546357 3674163583026727515426221)
                  ·
                    refine ⟨1377811343635022818284833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3674163583026727515426221 1377811343635022818284833)
                    ·
                      rfl

theorem cell22_4024917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_4024917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024917 prefixEnd_4024917 := by exact prefixLift 4024917
  have htrace : WordTrace (prefixWord ++ tailWord_4024917) baseStart_4024917 baseEnd_4024917 := by
    simpa [prefixWord, tailWord_4024917, baseEnd_4024917] using wordTrace_append hprefix tailTrace_4024917
  have hstable : (prefixWord ++ tailWord_4024917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024917).length < 2 ^ (prefixWord ++ tailWord_4024917).sum := by decide
  have hdescent : baseEnd_4024917 < baseStart_4024917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4024975 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 8]
def baseStart_4024975 : Nat := 118140960795 + 4024975 * 2 ^ 59
def prefixEnd_4024975 : Nat := 4983230072969 + 3 ^ 40 * 4024975 * 2
def baseEnd_4024975 : Nat := 459277066073443333444885

theorem tailTrace_4024975 : CollatzResearch.WordTrace tailWord_4024975 prefixEnd_4024975 459277066073443333444885 := by
  unfold tailWord_4024975
  simp only [CollatzResearch.WordTrace]
  refine ⟨146802898593210460847524379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97868599062140307231682919 146802898593210460847524379)
  ·
    refine ⟨220204347889815691271286569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146802898593210460847524379 220204347889815691271286569)
    ·
      refine ⟨165153260917361768453464927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220204347889815691271286569 165153260917361768453464927)
      ·
        refine ⟨247729891376042652680197391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165153260917361768453464927 247729891376042652680197391)
        ·
          refine ⟨371594837064063979020296087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247729891376042652680197391 371594837064063979020296087)
          ·
            refine ⟨557392255596095968530444131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371594837064063979020296087 557392255596095968530444131)
            ·
              refine ⟨836088383394143952795666197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557392255596095968530444131 836088383394143952795666197)
              ·
                refine ⟨39191642971600497787296853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 836088383394143952795666197 39191642971600497787296853)
                ·
                  refine ⟨459277066073443333444885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39191642971600497787296853 459277066073443333444885)
                  ·
                    rfl

theorem cell22_4024975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_4024975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4024975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4024975 prefixEnd_4024975 := by exact prefixLift 4024975
  have htrace : WordTrace (prefixWord ++ tailWord_4024975) baseStart_4024975 baseEnd_4024975 := by
    simpa [prefixWord, tailWord_4024975, baseEnd_4024975] using wordTrace_append hprefix tailTrace_4024975
  have hstable : (prefixWord ++ tailWord_4024975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4024975).length < 2 ^ (prefixWord ++ tailWord_4024975).sum := by decide
  have hdescent : baseEnd_4024975 < baseStart_4024975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4024975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025007 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 1, 5]
def baseStart_4025007 : Nat := 118140960795 + 4025007 * 2 ^ 59
def prefixEnd_4025007 : Nat := 4983230072969 + 3 ^ 40 * 4025007 * 2
def baseEnd_4025007 : Nat := 1377842152474292583534557

theorem tailTrace_4025007 : CollatzResearch.WordTrace tailWord_4025007 prefixEnd_4025007 1377842152474292583534557 := by
  unfold tailWord_4025007
  simp only [CollatzResearch.WordTrace]
  refine ⟨146804065729094530312689275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97869377152729686875126183 146804065729094530312689275)
  ·
    refine ⟨220206098593641795469033913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146804065729094530312689275 220206098593641795469033913)
    ·
      refine ⟨165154573945231346601775435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220206098593641795469033913 165154573945231346601775435)
      ·
        refine ⟨247731860917847019902663153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165154573945231346601775435 247731860917847019902663153)
        ·
          refine ⟨185798895688385264926997365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247731860917847019902663153 185798895688385264926997365)
          ·
            refine ⟨17418646470786118586906003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185798895688385264926997365 17418646470786118586906003)
            ·
              refine ⟨26127969706179177880359005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17418646470786118586906003 26127969706179177880359005)
              ·
                refine ⟨9797988639817191705134627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26127969706179177880359005 9797988639817191705134627)
                ·
                  refine ⟨14696982959725787557701941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9797988639817191705134627 14696982959725787557701941)
                  ·
                    refine ⟨1377842152474292583534557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14696982959725787557701941 1377842152474292583534557)
                    ·
                      rfl

theorem cell22_4025007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_4025007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025007 prefixEnd_4025007 := by exact prefixLift 4025007
  have htrace : WordTrace (prefixWord ++ tailWord_4025007) baseStart_4025007 baseEnd_4025007 := by
    simpa [prefixWord, tailWord_4025007, baseEnd_4025007] using wordTrace_append hprefix tailTrace_4025007
  have hstable : (prefixWord ++ tailWord_4025007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025007).length < 2 ^ (prefixWord ++ tailWord_4025007).sum := by decide
  have hdescent : baseEnd_4025007 < baseStart_4025007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025028 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4025028 : Nat := 118140960795 + 4025028 * 2 ^ 59
def prefixEnd_4025028 : Nat := 4983230072969 + 3 ^ 40 * 4025028 * 2
def baseEnd_4025028 : Nat := 1377849341203455528759493

theorem tailTrace_4025028 : CollatzResearch.WordTrace tailWord_4025028 prefixEnd_4025028 1377849341203455528759493 := by
  unfold tailWord_4025028
  simp only [CollatzResearch.WordTrace]
  refine ⟨73402415831009225449601869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97869887774678967266135825 73402415831009225449601869)
  ·
    refine ⟨27525905936628459543600701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73402415831009225449601869 27525905936628459543600701)
    ·
      refine ⟨10322214726235672328850263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27525905936628459543600701 10322214726235672328850263)
      ·
        refine ⟨15483322089353508493275395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10322214726235672328850263 15483322089353508493275395)
        ·
          refine ⟨23224983134030262739913093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15483322089353508493275395 23224983134030262739913093)
          ·
            refine ⟨4354684337630674263733705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23224983134030262739913093 4354684337630674263733705)
            ·
              refine ⟨3266013253223005697800279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4354684337630674263733705 3266013253223005697800279)
              ·
                refine ⟨4899019879834508546700419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266013253223005697800279 4899019879834508546700419)
                ·
                  refine ⟨7348529819751762820050629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899019879834508546700419 7348529819751762820050629)
                  ·
                    refine ⟨1377849341203455528759493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348529819751762820050629 1377849341203455528759493)
                    ·
                      rfl

theorem cell22_4025028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4025028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025028 prefixEnd_4025028 := by exact prefixLift 4025028
  have htrace : WordTrace (prefixWord ++ tailWord_4025028) baseStart_4025028 baseEnd_4025028 := by
    simpa [prefixWord, tailWord_4025028, baseEnd_4025028] using wordTrace_append hprefix tailTrace_4025028
  have hstable : (prefixWord ++ tailWord_4025028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025028).length < 2 ^ (prefixWord ++ tailWord_4025028).sum := by decide
  have hdescent : baseEnd_4025028 < baseStart_4025028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025077 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 4]
def baseStart_4025077 : Nat := 118140960795 + 4025077 * 2 ^ 59
def prefixEnd_4025077 : Nat := 4983230072969 + 3 ^ 40 * 4025077 * 2
def baseEnd_4025077 : Nat := 459288704968278578094781

theorem tailTrace_4025077 : CollatzResearch.WordTrace tailWord_4025077 prefixEnd_4025077 459288704968278578094781 := by
  unfold tailWord_4025077
  simp only [CollatzResearch.WordTrace]
  refine ⟨146806618838840932267737485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97871079225893954845158323 146806618838840932267737485)
  ·
    refine ⟨55052482064565349600401557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146806618838840932267737485 55052482064565349600401557)
    ·
      refine ⟨2580585096776500762518823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55052482064565349600401557 2580585096776500762518823)
      ·
        refine ⟨3870877645164751143778235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580585096776500762518823 3870877645164751143778235)
        ·
          refine ⟨5806316467747126715667353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870877645164751143778235 5806316467747126715667353)
          ·
            refine ⟨4354737350810345036750515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5806316467747126715667353 4354737350810345036750515)
            ·
              refine ⟨6532106026215517555125773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354737350810345036750515 6532106026215517555125773)
              ·
                refine ⟨2449539759830819083172165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6532106026215517555125773 2449539759830819083172165)
                ·
                  refine ⟨459288704968278578094781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449539759830819083172165 459288704968278578094781)
                  ·
                    rfl

theorem cell22_4025077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_4025077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025077 prefixEnd_4025077 := by exact prefixLift 4025077
  have htrace : WordTrace (prefixWord ++ tailWord_4025077) baseStart_4025077 baseEnd_4025077 := by
    simpa [prefixWord, tailWord_4025077, baseEnd_4025077] using wordTrace_append hprefix tailTrace_4025077
  have hstable : (prefixWord ++ tailWord_4025077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025077).length < 2 ^ (prefixWord ++ tailWord_4025077).sum := by decide
  have hdescent : baseEnd_4025077 < baseStart_4025077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025082 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_4025082 : Nat := 118140960795 + 4025082 * 2 ^ 59
def prefixEnd_4025082 : Nat := 4983230072969 + 3 ^ 40 * 4025082 * 2
def baseEnd_4025082 : Nat := 459289275502339129303109

theorem tailTrace_4025082 : CollatzResearch.WordTrace tailWord_4025082 prefixEnd_4025082 459289275502339129303109 := by
  unfold tailWord_4025082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36701700300955704530417375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97871200802548545414446333 36701700300955704530417375)
  ·
    refine ⟨55052550451433556795626063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36701700300955704530417375 55052550451433556795626063)
    ·
      refine ⟨82578825677150335193439095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55052550451433556795626063 82578825677150335193439095)
      ·
        refine ⟨123868238515725502790158643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82578825677150335193439095 123868238515725502790158643)
        ·
          refine ⟨185802357773588254185237965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123868238515725502790158643 185802357773588254185237965)
          ·
            refine ⟨69675884165095595319464237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185802357773588254185237965 69675884165095595319464237)
            ·
              refine ⟨26128456561910848244799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69675884165095595319464237 26128456561910848244799089)
              ·
                refine ⟨19596342421433136183599317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26128456561910848244799089 19596342421433136183599317)
                ·
                  refine ⟨459289275502339129303109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19596342421433136183599317 459289275502339129303109)
                  ·
                    rfl

theorem cell22_4025082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_4025082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025082 prefixEnd_4025082 := by exact prefixLift 4025082
  have htrace : WordTrace (prefixWord ++ tailWord_4025082) baseStart_4025082 baseEnd_4025082 := by
    simpa [prefixWord, tailWord_4025082, baseEnd_4025082] using wordTrace_append hprefix tailTrace_4025082
  have hstable : (prefixWord ++ tailWord_4025082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025082).length < 2 ^ (prefixWord ++ tailWord_4025082).sum := by decide
  have hdescent : baseEnd_4025082 < baseStart_4025082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025097 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_4025097 : Nat := 118140960795 + 4025097 * 2 ^ 59
def prefixEnd_4025097 : Nat := 4983230072969 + 3 ^ 40 * 4025097 * 2
def baseEnd_4025097 : Nat := 1377872961313562348784281

theorem tailTrace_4025097 : CollatzResearch.WordTrace tailWord_4025097 prefixEnd_4025097 1377872961313562348784281 := by
  unfold tailWord_4025097
  simp only [CollatzResearch.WordTrace]
  refine ⟨146807348298768475683465545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97871565532512317122310363 146807348298768475683465545)
  ·
    refine ⟨110105511224076356762599159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146807348298768475683465545 110105511224076356762599159)
    ·
      refine ⟨165158266836114535143898739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110105511224076356762599159 165158266836114535143898739)
      ·
        refine ⟨247737400254171802715848109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165158266836114535143898739 247737400254171802715848109)
        ·
          refine ⟨92901525095314426018443041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247737400254171802715848109 92901525095314426018443041)
          ·
            refine ⟨69676143821485819513832281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92901525095314426018443041 69676143821485819513832281)
            ·
              refine ⟨52257107866114364635374211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69676143821485819513832281 52257107866114364635374211)
              ·
                refine ⟨78385661799171546953061317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52257107866114364635374211 78385661799171546953061317)
                ·
                  refine ⟨14697311587344665053698997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78385661799171546953061317 14697311587344665053698997)
                  ·
                    refine ⟨1377872961313562348784281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14697311587344665053698997 1377872961313562348784281)
                    ·
                      rfl

theorem cell22_4025097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_4025097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025097 prefixEnd_4025097 := by exact prefixLift 4025097
  have htrace : WordTrace (prefixWord ++ tailWord_4025097) baseStart_4025097 baseEnd_4025097 := by
    simpa [prefixWord, tailWord_4025097, baseEnd_4025097] using wordTrace_append hprefix tailTrace_4025097
  have hstable : (prefixWord ++ tailWord_4025097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025097).length < 2 ^ (prefixWord ++ tailWord_4025097).sum := by decide
  have hdescent : baseEnd_4025097 < baseStart_4025097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025103 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 1, 3]
def baseStart_4025103 : Nat := 118140960795 + 4025103 * 2 ^ 59
def prefixEnd_4025103 : Nat := 4983230072969 + 3 ^ 40 * 4025103 * 2
def baseEnd_4025103 : Nat := 1377875015236180333134263

theorem tailTrace_4025103 : CollatzResearch.WordTrace tailWord_4025103 prefixEnd_4025103 1377875015236180333134263 := by
  unfold tailWord_4025103
  simp only [CollatzResearch.WordTrace]
  refine ⟨146807567136746738708183963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97871711424497825805455975 146807567136746738708183963)
  ·
    refine ⟨220211350705120108062275945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146807567136746738708183963 220211350705120108062275945)
    ·
      refine ⟨165158513028840081046706959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220211350705120108062275945 165158513028840081046706959)
      ·
        refine ⟨247737769543260121570060439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165158513028840081046706959 247737769543260121570060439)
        ·
          refine ⟨371606654314890182355090659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247737769543260121570060439 371606654314890182355090659)
          ·
            refine ⟨557409981472335273532635989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371606654314890182355090659 557409981472335273532635989)
            ·
              refine ⟨3266074110189464493355289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 557409981472335273532635989 3266074110189464493355289)
              ·
                refine ⟨2449555582642098370016467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266074110189464493355289 2449555582642098370016467)
                ·
                  refine ⟨3674333373963147555024701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449555582642098370016467 3674333373963147555024701)
                  ·
                    refine ⟨1377875015236180333134263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3674333373963147555024701 1377875015236180333134263)
                    ·
                      rfl

theorem cell22_4025103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_4025103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025103 prefixEnd_4025103 := by exact prefixLift 4025103
  have htrace : WordTrace (prefixWord ++ tailWord_4025103) baseStart_4025103 baseEnd_4025103 := by
    simpa [prefixWord, tailWord_4025103, baseEnd_4025103] using wordTrace_append hprefix tailTrace_4025103
  have hstable : (prefixWord ++ tailWord_4025103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025103).length < 2 ^ (prefixWord ++ tailWord_4025103).sum := by decide
  have hdescent : baseEnd_4025103 < baseStart_4025103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025112 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_4025112 : Nat := 118140960795 + 4025112 * 2 ^ 59
def prefixEnd_4025112 : Nat := 4983230072969 + 3 ^ 40 * 4025112 * 2
def baseEnd_4025112 : Nat := 1377878096120107309659235

theorem tailTrace_4025112 : CollatzResearch.WordTrace tailWord_4025112 prefixEnd_4025112 1377878096120107309659235 := by
  unfold tailWord_4025112
  simp only [CollatzResearch.WordTrace]
  refine ⟨73403947696857066622630795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97871930262476088830174393 73403947696857066622630795)
  ·
    refine ⟨110105921545285599933946193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73403947696857066622630795 110105921545285599933946193)
    ·
      refine ⟨82579441158964199950459645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110105921545285599933946193 82579441158964199950459645)
      ·
        refine ⟨30967290434611574981422367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82579441158964199950459645 30967290434611574981422367)
        ·
          refine ⟨46450935651917362472133551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30967290434611574981422367 46450935651917362472133551)
          ·
            refine ⟨69676403477876043708200327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46450935651917362472133551 69676403477876043708200327)
            ·
              refine ⟨104514605216814065562300491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69676403477876043708200327 104514605216814065562300491)
              ·
                refine ⟨156771907825221098343450737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104514605216814065562300491 156771907825221098343450737)
                ·
                  refine ⟨117578930868915823757588053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156771907825221098343450737 117578930868915823757588053)
                  ·
                    refine ⟨1377878096120107309659235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117578930868915823757588053 1377878096120107309659235)
                    ·
                      rfl

theorem cell22_4025112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_4025112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025112 prefixEnd_4025112 := by exact prefixLift 4025112
  have htrace : WordTrace (prefixWord ++ tailWord_4025112) baseStart_4025112 baseEnd_4025112 := by
    simpa [prefixWord, tailWord_4025112, baseEnd_4025112] using wordTrace_append hprefix tailTrace_4025112
  have hstable : (prefixWord ++ tailWord_4025112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025112).length < 2 ^ (prefixWord ++ tailWord_4025112).sum := by decide
  have hdescent : baseEnd_4025112 < baseStart_4025112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025116 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 5]
def baseStart_4025116 : Nat := 118140960795 + 4025116 * 2 ^ 59
def prefixEnd_4025116 : Nat := 4983230072969 + 3 ^ 40 * 4025116 * 2
def baseEnd_4025116 : Nat := 459293155133950877519741

theorem tailTrace_4025116 : CollatzResearch.WordTrace tailWord_4025116 prefixEnd_4025116 459293155133950877519741 := by
  unfold tailWord_4025116
  simp only [CollatzResearch.WordTrace]
  refine ⟨73404020642849820964203601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97872027523799761285604801 73404020642849820964203601)
  ·
    refine ⟨55053015482137365723152701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73404020642849820964203601 55053015482137365723152701)
    ·
      refine ⟨20644880805801512146182263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55053015482137365723152701 20644880805801512146182263)
      ·
        refine ⟨30967321208702268219273395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20644880805801512146182263 30967321208702268219273395)
        ·
          refine ⟨46450981813053402328910093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30967321208702268219273395 46450981813053402328910093)
          ·
            refine ⟨17419118179895025873341285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46450981813053402328910093 17419118179895025873341285)
            ·
              refine ⟨3266084658730317351251491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17419118179895025873341285 3266084658730317351251491)
              ·
                refine ⟨4899126988095476026877237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266084658730317351251491 4899126988095476026877237)
                ·
                  refine ⟨459293155133950877519741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899126988095476026877237 459293155133950877519741)
                  ·
                    rfl

theorem cell22_4025116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_4025116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025116 prefixEnd_4025116 := by exact prefixLift 4025116
  have htrace : WordTrace (prefixWord ++ tailWord_4025116) baseStart_4025116 baseEnd_4025116 := by
    simpa [prefixWord, tailWord_4025116, baseEnd_4025116] using wordTrace_append hprefix tailTrace_4025116
  have hstable : (prefixWord ++ tailWord_4025116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025116).length < 2 ^ (prefixWord ++ tailWord_4025116).sum := by decide
  have hdescent : baseEnd_4025116 < baseStart_4025116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025161 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 4]
def baseStart_4025161 : Nat := 118140960795 + 4025161 * 2 ^ 59
def prefixEnd_4025161 : Nat := 4983230072969 + 3 ^ 40 * 4025161 * 2
def baseEnd_4025161 : Nat := 459298289940495838394695

theorem tailTrace_4025161 : CollatzResearch.WordTrace tailWord_4025161 prefixEnd_4025161 459298289940495838394695 := by
  unfold tailWord_4025161
  simp only [CollatzResearch.WordTrace]
  refine ⟨146809682570536614613795337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97873121713691076409196891 146809682570536614613795337)
  ·
    refine ⟨110107261927902460960346503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146809682570536614613795337 110107261927902460960346503)
    ·
      refine ⟨165160892891853691440519755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110107261927902460960346503 165160892891853691440519755)
      ·
        refine ⟨247741339337780537160779633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165160892891853691440519755 247741339337780537160779633)
        ·
          refine ⟨185806004503335402870584725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247741339337780537160779633 185806004503335402870584725)
          ·
            refine ⟨8709656461093847009558659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185806004503335402870584725 8709656461093847009558659)
            ·
              refine ⟨13064484691640770514337989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709656461093847009558659 13064484691640770514337989)
              ·
                refine ⟨2449590879682644471438373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13064484691640770514337989 2449590879682644471438373)
                ·
                  refine ⟨459298289940495838394695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449590879682644471438373 459298289940495838394695)
                  ·
                    rfl

theorem cell22_4025161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_4025161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025161 prefixEnd_4025161 := by exact prefixLift 4025161
  have htrace : WordTrace (prefixWord ++ tailWord_4025161) baseStart_4025161 baseEnd_4025161 := by
    simpa [prefixWord, tailWord_4025161, baseEnd_4025161] using wordTrace_append hprefix tailTrace_4025161
  have hstable : (prefixWord ++ tailWord_4025161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025161).length < 2 ^ (prefixWord ++ tailWord_4025161).sum := by decide
  have hdescent : baseEnd_4025161 < baseStart_4025161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025191 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4025191 : Nat := 118140960795 + 4025191 * 2 ^ 59
def prefixEnd_4025191 : Nat := 4983230072969 + 3 ^ 40 * 4025191 * 2
def baseEnd_4025191 : Nat := 1377905139434577436933993

theorem tailTrace_4025191 : CollatzResearch.WordTrace tailWord_4025191 prefixEnd_4025191 1377905139434577436933993 := by
  unfold tailWord_4025191
  simp only [CollatzResearch.WordTrace]
  refine ⟨146810776760427929737387427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97873851173618619824924951 146810776760427929737387427)
  ·
    refine ⟨220216165140641894606081141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146810776760427929737387427 220216165140641894606081141)
    ·
      refine ⟨20645265481935177619320107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220216165140641894606081141 20645265481935177619320107)
      ·
        refine ⟨30967898222902766428980161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20645265481935177619320107 30967898222902766428980161)
        ·
          refine ⟨23225923667177074821735121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30967898222902766428980161 23225923667177074821735121)
          ·
            refine ⟨17419442750382806116301341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23225923667177074821735121 17419442750382806116301341)
            ·
              refine ⟨6532291031393552293613003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17419442750382806116301341 6532291031393552293613003)
              ·
                refine ⟨9798436547090328440419505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532291031393552293613003 9798436547090328440419505)
                ·
                  refine ⟨7348827410317746330314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9798436547090328440419505 7348827410317746330314629)
                  ·
                    refine ⟨1377905139434577436933993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348827410317746330314629 1377905139434577436933993)
                    ·
                      rfl

theorem cell22_4025191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4025191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025191 prefixEnd_4025191 := by exact prefixLift 4025191
  have htrace : WordTrace (prefixWord ++ tailWord_4025191) baseStart_4025191 baseEnd_4025191 := by
    simpa [prefixWord, tailWord_4025191, baseEnd_4025191] using wordTrace_append hprefix tailTrace_4025191
  have hstable : (prefixWord ++ tailWord_4025191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025191).length < 2 ^ (prefixWord ++ tailWord_4025191).sum := by decide
  have hdescent : baseEnd_4025191 < baseStart_4025191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025206 : List Nat := [5, 1, 1, 3, 1, 2, 9]
def baseStart_4025206 : Nat := 118140960795 + 4025206 * 2 ^ 59
def prefixEnd_4025206 : Nat := 4983230072969 + 3 ^ 40 * 4025206 * 2
def baseEnd_4025206 : Nat := 51033713860782311029961

theorem tailTrace_4025206 : CollatzResearch.WordTrace tailWord_4025206 prefixEnd_4025206 51033713860782311029961 := by
  unfold tailWord_4025206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9175707740960849206198967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97874215903582391532788981 9175707740960849206198967)
  ·
    refine ⟨13763561611441273809298451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9175707740960849206198967 13763561611441273809298451)
    ·
      refine ⟨20645342417161910713947677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13763561611441273809298451 20645342417161910713947677)
      ·
        refine ⟨7742003406435716517730379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20645342417161910713947677 7742003406435716517730379)
        ·
          refine ⟨11613005109653574776595569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742003406435716517730379 11613005109653574776595569)
          ·
            refine ⟨8709753832240181082446677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613005109653574776595569 8709753832240181082446677)
            ·
              refine ⟨51033713860782311029961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8709753832240181082446677 51033713860782311029961)
              ·
                rfl

theorem cell22_4025206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 9].length) (baseStart_4025206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025206 prefixEnd_4025206 := by exact prefixLift 4025206
  have htrace : WordTrace (prefixWord ++ tailWord_4025206) baseStart_4025206 baseEnd_4025206 := by
    simpa [prefixWord, tailWord_4025206, baseEnd_4025206] using wordTrace_append hprefix tailTrace_4025206
  have hstable : (prefixWord ++ tailWord_4025206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025206).length < 2 ^ (prefixWord ++ tailWord_4025206).sum := by decide
  have hdescent : baseEnd_4025206 < baseStart_4025206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025221 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_4025221 : Nat := 118140960795 + 4025221 * 2 ^ 59
def prefixEnd_4025221 : Nat := 4983230072969 + 3 ^ 40 * 4025221 * 2
def baseEnd_4025221 : Nat := 1377915409047667358683901

theorem tailTrace_4025221 : CollatzResearch.WordTrace tailWord_4025221 prefixEnd_4025221 1377915409047667358683901 := by
  unfold tailWord_4025221
  simp only [CollatzResearch.WordTrace]
  refine ⟨146811870950319244860979517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97874580633546163240653011 146811870950319244860979517)
  ·
    refine ⟨55054451606369716822867319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146811870950319244860979517 55054451606369716822867319)
    ·
      refine ⟨82581677409554575234300979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55054451606369716822867319 82581677409554575234300979)
      ·
        refine ⟨123872516114331862851451469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82581677409554575234300979 123872516114331862851451469)
        ·
          refine ⟨46452193542874448569294301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123872516114331862851451469 46452193542874448569294301)
          ·
            refine ⟨17419572578577918213485363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46452193542874448569294301 17419572578577918213485363)
            ·
              refine ⟨26129358867866877320228045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17419572578577918213485363 26129358867866877320228045)
              ·
                refine ⟨9798509575450078995085517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26129358867866877320228045 9798509575450078995085517)
                ·
                  refine ⟨3674441090793779623157069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9798509575450078995085517 3674441090793779623157069)
                  ·
                    refine ⟨1377915409047667358683901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3674441090793779623157069 1377915409047667358683901)
                    ·
                      rfl

theorem cell22_4025221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_4025221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025221 prefixEnd_4025221 := by exact prefixLift 4025221
  have htrace : WordTrace (prefixWord ++ tailWord_4025221) baseStart_4025221 baseEnd_4025221 := by
    simpa [prefixWord, tailWord_4025221, baseEnd_4025221] using wordTrace_append hprefix tailTrace_4025221
  have hstable : (prefixWord ++ tailWord_4025221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025221).length < 2 ^ (prefixWord ++ tailWord_4025221).sum := by decide
  have hdescent : baseEnd_4025221 < baseStart_4025221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025268 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_4025268 : Nat := 118140960795 + 4025268 * 2 ^ 59
def prefixEnd_4025268 : Nat := 4983230072969 + 3 ^ 40 * 4025268 * 2
def baseEnd_4025268 : Nat := 459310499369391634252919

theorem tailTrace_4025268 : CollatzResearch.WordTrace tailWord_4025268 prefixEnd_4025268 459310499369391634252919 := by
  unfold tailWord_4025268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73406792590574485943970229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97875723454099314591960305 73406792590574485943970229)
  ·
    refine ⟨6881886805366358057247209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73406792590574485943970229 6881886805366358057247209)
    ·
      refine ⟨5161415104024768542935407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6881886805366358057247209 5161415104024768542935407)
      ·
        refine ⟨7742122656037152814403111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161415104024768542935407 7742122656037152814403111)
        ·
          refine ⟨11613183984055729221604667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742122656037152814403111 11613183984055729221604667)
          ·
            refine ⟨17419775976083593832407001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11613183984055729221604667 17419775976083593832407001)
            ·
              refine ⟨13064831982062695374305251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17419775976083593832407001 13064831982062695374305251)
              ·
                refine ⟨19597247973094043061457877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13064831982062695374305251 19597247973094043061457877)
                ·
                  refine ⟨459310499369391634252919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19597247973094043061457877 459310499369391634252919)
                  ·
                    rfl

theorem cell22_4025268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_4025268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025268 prefixEnd_4025268 := by exact prefixLift 4025268
  have htrace : WordTrace (prefixWord ++ tailWord_4025268) baseStart_4025268 baseEnd_4025268 := by
    simpa [prefixWord, tailWord_4025268, baseEnd_4025268] using wordTrace_append hprefix tailTrace_4025268
  have hstable : (prefixWord ++ tailWord_4025268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025268).length < 2 ^ (prefixWord ++ tailWord_4025268).sum := by decide
  have hdescent : baseEnd_4025268 < baseStart_4025268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025279 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 6]
def baseStart_4025279 : Nat := 118140960795 + 4025279 * 2 ^ 59
def prefixEnd_4025279 : Nat := 4983230072969 + 3 ^ 40 * 4025279 * 2
def baseEnd_4025279 : Nat := 459311754544324846911241

theorem tailTrace_4025279 : CollatzResearch.WordTrace tailWord_4025279 prefixEnd_4025279 459311754544324846911241 := by
  unfold tailWord_4025279
  simp only [CollatzResearch.WordTrace]
  refine ⟨146813986384109120766590891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97875990922739413844393927 146813986384109120766590891)
  ·
    refine ⟨220220979576163681149886337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146813986384109120766590891 220220979576163681149886337)
    ·
      refine ⟨165165734682122760862414753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220220979576163681149886337 165165734682122760862414753)
      ·
        refine ⟨123874301011592070646811065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165165734682122760862414753 123874301011592070646811065)
        ·
          refine ⟨92905725758694052985108299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123874301011592070646811065 92905725758694052985108299)
          ·
            refine ⟨139358588638041079477662449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92905725758694052985108299 139358588638041079477662449)
            ·
              refine ⟨104518941478530809608246837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139358588638041079477662449 104518941478530809608246837)
              ·
                refine ⟨9798650763612263400773141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104518941478530809608246837 9798650763612263400773141)
                ·
                  refine ⟨459311754544324846911241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9798650763612263400773141 459311754544324846911241)
                  ·
                    rfl

theorem cell22_4025279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 6].length) (baseStart_4025279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025279 prefixEnd_4025279 := by exact prefixLift 4025279
  have htrace : WordTrace (prefixWord ++ tailWord_4025279) baseStart_4025279 baseEnd_4025279 := by
    simpa [prefixWord, tailWord_4025279, baseEnd_4025279] using wordTrace_append hprefix tailTrace_4025279
  have hstable : (prefixWord ++ tailWord_4025279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025279).length < 2 ^ (prefixWord ++ tailWord_4025279).sum := by decide
  have hdescent : baseEnd_4025279 < baseStart_4025279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025298 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_4025298 : Nat := 118140960795 + 4025298 * 2 ^ 59
def prefixEnd_4025298 : Nat := 4983230072969 + 3 ^ 40 * 4025298 * 2
def baseEnd_4025298 : Nat := 1377941767721264824508665

theorem tailTrace_4025298 : CollatzResearch.WordTrace tailWord_4025298 prefixEnd_4025298 1377941767721264824508665 := by
  unfold tailWord_4025298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36703669842760071752883137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97876452914026858007688365 36703669842760071752883137)
  ·
    refine ⟨27527752382070053814662353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36703669842760071752883137 27527752382070053814662353)
    ·
      refine ⟨20645814286552540360996765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27527752382070053814662353 20645814286552540360996765)
      ·
        refine ⟨7742180357457202635373787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20645814286552540360996765 7742180357457202635373787)
        ·
          refine ⟨11613270536185803953060681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742180357457202635373787 11613270536185803953060681)
          ·
            refine ⟨8709952902139352964795511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613270536185803953060681 8709952902139352964795511)
            ·
              refine ⟨13064929353209029447193267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709952902139352964795511 13064929353209029447193267)
              ·
                refine ⟨19597394029813544170789901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13064929353209029447193267 19597394029813544170789901)
                ·
                  refine ⟨7349022761180079064046213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19597394029813544170789901 7349022761180079064046213)
                  ·
                    refine ⟨1377941767721264824508665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7349022761180079064046213 1377941767721264824508665)
                    ·
                      rfl

theorem cell22_4025298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_4025298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025298 prefixEnd_4025298 := by exact prefixLift 4025298
  have htrace : WordTrace (prefixWord ++ tailWord_4025298) baseStart_4025298 baseEnd_4025298 := by
    simpa [prefixWord, tailWord_4025298, baseEnd_4025298] using wordTrace_append hprefix tailTrace_4025298
  have hstable : (prefixWord ++ tailWord_4025298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025298).length < 2 ^ (prefixWord ++ tailWord_4025298).sum := by decide
  have hdescent : baseEnd_4025298 < baseStart_4025298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025339 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_4025339 : Nat := 118140960795 + 4025339 * 2 ^ 59
def prefixEnd_4025339 : Nat := 4983230072969 + 3 ^ 40 * 4025339 * 2
def baseEnd_4025339 : Nat := 1377955802859154384233539

theorem tailTrace_4025339 : CollatzResearch.WordTrace tailWord_4025339 prefixEnd_4025339 1377955802859154384233539 := by
  unfold tailWord_4025339
  simp only [CollatzResearch.WordTrace]
  refine ⟨146816174763891751013775071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97877449842594500675850047 146816174763891751013775071)
  ·
    refine ⟨220224262145837626520662607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146816174763891751013775071 220224262145837626520662607)
    ·
      refine ⟨330336393218756439780993911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220224262145837626520662607 330336393218756439780993911)
      ·
        refine ⟨495504589828134659671490867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330336393218756439780993911 495504589828134659671490867)
        ·
          refine ⟨743256884742201989507236301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495504589828134659671490867 743256884742201989507236301)
          ·
            refine ⟨278721331778325746065213613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743256884742201989507236301 278721331778325746065213613)
            ·
              refine ⟨104520499416872154774455105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278721331778325746065213613 104520499416872154774455105)
              ·
                refine ⟨78390374562654116080841329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104520499416872154774455105 78390374562654116080841329)
                ·
                  refine ⟨58792780921990587060630997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78390374562654116080841329 58792780921990587060630997)
                  ·
                    refine ⟨1377955802859154384233539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58792780921990587060630997 1377955802859154384233539)
                    ·
                      rfl

theorem cell22_4025339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_4025339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025339 prefixEnd_4025339 := by exact prefixLift 4025339
  have htrace : WordTrace (prefixWord ++ tailWord_4025339) baseStart_4025339 baseEnd_4025339 := by
    simpa [prefixWord, tailWord_4025339, baseEnd_4025339] using wordTrace_append hprefix tailTrace_4025339
  have hstable : (prefixWord ++ tailWord_4025339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025339).length < 2 ^ (prefixWord ++ tailWord_4025339).sum := by decide
  have hdescent : baseEnd_4025339 < baseStart_4025339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025358 : List Nat := [4, 1, 1, 2, 2, 3, 3, 6]
def baseStart_4025358 : Nat := 118140960795 + 4025358 * 2 ^ 59
def prefixEnd_4025358 : Nat := 4983230072969 + 3 ^ 40 * 4025358 * 2
def baseEnd_4025358 : Nat := 153106922994160518667609

theorem tailTrace_4025358 : CollatzResearch.WordTrace tailWord_4025358 prefixEnd_4025358 153106922994160518667609 := by
  unfold tailWord_4025358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352108468852864657339591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97877911833881944839144485 18352108468852864657339591)
  ·
    refine ⟨27528162703279296986009387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18352108468852864657339591 27528162703279296986009387)
    ·
      refine ⟨41292244054918945479014081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27528162703279296986009387 41292244054918945479014081)
      ·
        refine ⟨30969183041189209109260561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41292244054918945479014081 30969183041189209109260561)
        ·
          refine ⟨23226887280891906831945421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30969183041189209109260561 23226887280891906831945421)
          ·
            refine ⟨8710082730334465061979533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23226887280891906831945421 8710082730334465061979533)
            ·
              refine ⟨3266281023875424398242325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8710082730334465061979533 3266281023875424398242325)
              ·
                refine ⟨153106922994160518667609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3266281023875424398242325 153106922994160518667609)
                ·
                  rfl

theorem cell22_4025358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_4025358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025358 prefixEnd_4025358 := by exact prefixLift 4025358
  have htrace : WordTrace (prefixWord ++ tailWord_4025358) baseStart_4025358 baseEnd_4025358 := by
    simpa [prefixWord, tailWord_4025358, baseEnd_4025358] using wordTrace_append hprefix tailTrace_4025358
  have hstable : (prefixWord ++ tailWord_4025358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025358).length < 2 ^ (prefixWord ++ tailWord_4025358).sum := by decide
  have hdescent : baseEnd_4025358 < baseStart_4025358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025390 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_4025390 : Nat := 118140960795 + 4025390 * 2 ^ 59
def prefixEnd_4025390 : Nat := 4983230072969 + 3 ^ 40 * 4025390 * 2
def baseEnd_4025390 : Nat := 1377973261201407251208383

theorem tailTrace_4025390 : CollatzResearch.WordTrace tailWord_4025390 prefixEnd_4025390 1377973261201407251208383 := by
  unfold tailWord_4025390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352254360838373340485203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97878689924471324482587749 18352254360838373340485203)
  ·
    refine ⟨27528381541257560010727805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18352254360838373340485203 27528381541257560010727805)
    ·
      refine ⟨10323143077971585004022927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27528381541257560010727805 10323143077971585004022927)
      ·
        refine ⟨15484714616957377506034391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10323143077971585004022927 15484714616957377506034391)
        ·
          refine ⟨23227071925436066259051587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15484714616957377506034391 23227071925436066259051587)
          ·
            refine ⟨34840607888154099388577381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23227071925436066259051587 34840607888154099388577381)
            ·
              refine ⟨6532613979028893635358259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34840607888154099388577381 6532613979028893635358259)
              ·
                refine ⟨9798920968543340453037389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532613979028893635358259 9798920968543340453037389)
                ·
                  refine ⟨3674595363203752669889021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9798920968543340453037389 3674595363203752669889021)
                  ·
                    refine ⟨1377973261201407251208383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3674595363203752669889021 1377973261201407251208383)
                    ·
                      rfl

theorem cell22_4025390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_4025390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025390 prefixEnd_4025390 := by exact prefixLift 4025390
  have htrace : WordTrace (prefixWord ++ tailWord_4025390) baseStart_4025390 baseEnd_4025390 := by
    simpa [prefixWord, tailWord_4025390, baseEnd_4025390] using wordTrace_append hprefix tailTrace_4025390
  have hstable : (prefixWord ++ tailWord_4025390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025390).length < 2 ^ (prefixWord ++ tailWord_4025390).sum := by decide
  have hdescent : baseEnd_4025390 < baseStart_4025390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025480 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_4025480 : Nat := 118140960795 + 4025480 * 2 ^ 59
def prefixEnd_4025480 : Nat := 4983230072969 + 3 ^ 40 * 4025480 * 2
def baseEnd_4025480 : Nat := 1378004070040677016458107

theorem tailTrace_4025480 : CollatzResearch.WordTrace tailWord_4025480 prefixEnd_4025480 1378004070040677016458107 := by
  unfold tailWord_4025480
  simp only [CollatzResearch.WordTrace]
  refine ⟨73410658728190466047328947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97880878304253954729771929 73410658728190466047328947)
  ·
    refine ⟨110115988092285699070993421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73410658728190466047328947 110115988092285699070993421)
    ·
      refine ⟨41293495534607137151622533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110115988092285699070993421 41293495534607137151622533)
      ·
        refine ⟨7742530412738838215929225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41293495534607137151622533 7742530412738838215929225)
        ·
          refine ⟨5806897809554128661946919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7742530412738838215929225 5806897809554128661946919)
          ·
            refine ⟨8710346714331192992920379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806897809554128661946919 8710346714331192992920379)
            ·
              refine ⟨13065520071496789489380569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710346714331192992920379 13065520071496789489380569)
              ·
                refine ⟨9799140053622592117035427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13065520071496789489380569 9799140053622592117035427)
                ·
                  refine ⟨14698710080433888175553141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9799140053622592117035427 14698710080433888175553141)
                  ·
                    refine ⟨1378004070040677016458107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14698710080433888175553141 1378004070040677016458107)
                    ·
                      rfl

theorem cell22_4025480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_4025480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025480 prefixEnd_4025480 := by exact prefixLift 4025480
  have htrace : WordTrace (prefixWord ++ tailWord_4025480) baseStart_4025480 baseEnd_4025480 := by
    simpa [prefixWord, tailWord_4025480, baseEnd_4025480] using wordTrace_append hprefix tailTrace_4025480
  have hstable : (prefixWord ++ tailWord_4025480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025480).length < 2 ^ (prefixWord ++ tailWord_4025480).sum := by decide
  have hdescent : baseEnd_4025480 < baseStart_4025480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025617 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 4]
def baseStart_4025617 : Nat := 118140960795 + 4025617 * 2 ^ 59
def prefixEnd_4025617 : Nat := 4983230072969 + 3 ^ 40 * 4025617 * 2
def baseEnd_4025617 : Nat := 459350322646818108594229

theorem tailTrace_4025617 : CollatzResearch.WordTrace tailWord_4025617 prefixEnd_4025617 459350322646818108594229 := by
  unfold tailWord_4025617
  simp only [CollatzResearch.WordTrace]
  refine ⟨146826314256884604492395105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97884209504589736328263403 146826314256884604492395105)
  ·
    refine ⟨110119735692663453369296329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146826314256884604492395105 110119735692663453369296329)
    ·
      refine ⟨82589801769497590026972247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110119735692663453369296329 82589801769497590026972247)
      ·
        refine ⟨123884702654246385040458371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82589801769497590026972247 123884702654246385040458371)
        ·
          refine ⟨185827053981369577560687557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123884702654246385040458371 185827053981369577560687557)
          ·
            refine ⟨34842572621506795792628917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185827053981369577560687557 34842572621506795792628917)
            ·
              refine ⟨3266491183266262105558961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34842572621506795792628917 3266491183266262105558961)
              ·
                refine ⟨2449868387449696579169221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266491183266262105558961 2449868387449696579169221)
                ·
                  refine ⟨459350322646818108594229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449868387449696579169221 459350322646818108594229)
                  ·
                    rfl

theorem cell22_4025617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_4025617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025617 prefixEnd_4025617 := by exact prefixLift 4025617
  have htrace : WordTrace (prefixWord ++ tailWord_4025617) baseStart_4025617 baseEnd_4025617 := by
    simpa [prefixWord, tailWord_4025617, baseEnd_4025617] using wordTrace_append hprefix tailTrace_4025617
  have hstable : (prefixWord ++ tailWord_4025617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025617).length < 2 ^ (prefixWord ++ tailWord_4025617).sum := by decide
  have hdescent : baseEnd_4025617 < baseStart_4025617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025628 : List Nat := [2, 2, 3, 1, 1, 1, 3, 9]
def baseStart_4025628 : Nat := 118140960795 + 4025628 * 2 ^ 59
def prefixEnd_4025628 : Nat := 4983230072969 + 3 ^ 40 * 4025628 * 2
def baseEnd_4025628 : Nat := 153117192607250440417517

theorem tailTrace_4025628 : CollatzResearch.WordTrace tailWord_4025628 prefixEnd_4025628 153117192607250440417517 := by
  unfold tailWord_4025628
  simp only [CollatzResearch.WordTrace]
  refine ⟨73413357729922376685522769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97884476973229835580697025 73413357729922376685522769)
  ·
    refine ⟨55060018297441782514142077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73413357729922376685522769 55060018297441782514142077)
    ·
      refine ⟨20647506861540668442803279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55060018297441782514142077 20647506861540668442803279)
      ·
        refine ⟨30971260292311002664204919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20647506861540668442803279 30971260292311002664204919)
        ·
          refine ⟨46456890438466503996307379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30971260292311002664204919 46456890438466503996307379)
          ·
            refine ⟨69685335657699755994461069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46456890438466503996307379 69685335657699755994461069)
            ·
              refine ⟨26132000871637408497922901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69685335657699755994461069 26132000871637408497922901)
              ·
                refine ⟨153117192607250440417517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26132000871637408497922901 153117192607250440417517)
                ·
                  rfl

theorem cell22_4025628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_4025628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025628 prefixEnd_4025628 := by exact prefixLift 4025628
  have htrace : WordTrace (prefixWord ++ tailWord_4025628) baseStart_4025628 baseEnd_4025628 := by
    simpa [prefixWord, tailWord_4025628, baseEnd_4025628] using wordTrace_append hprefix tailTrace_4025628
  have hstable : (prefixWord ++ tailWord_4025628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025628).length < 2 ^ (prefixWord ++ tailWord_4025628).sum := by decide
  have hdescent : baseEnd_4025628 < baseStart_4025628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025673 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 7]
def baseStart_4025673 : Nat := 118140960795 + 4025673 * 2 ^ 59
def prefixEnd_4025673 : Nat := 4983230072969 + 3 ^ 40 * 4025673 * 2
def baseEnd_4025673 : Nat := 459356712628296282127505

theorem tailTrace_4025673 : CollatzResearch.WordTrace tailWord_4025673 prefixEnd_4025673 459356712628296282127505 := by
  unfold tailWord_4025673
  simp only [CollatzResearch.WordTrace]
  refine ⟨146828356744681726056433673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97885571163121150704289115 146828356744681726056433673)
  ·
    refine ⟨110121267558511294542325255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146828356744681726056433673 110121267558511294542325255)
    ·
      refine ⟨165181901337766941813487883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110121267558511294542325255 165181901337766941813487883)
      ·
        refine ⟨247772852006650412720231825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165181901337766941813487883 247772852006650412720231825)
        ·
          refine ⟨185829639004987809540173869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247772852006650412720231825 185829639004987809540173869)
          ·
            refine ⟨69686114626870428577565201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185829639004987809540173869 69686114626870428577565201)
            ·
              refine ⟨52264585970152821433173901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69686114626870428577565201 52264585970152821433173901)
              ·
                refine ⟨19599219738807308037440213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52264585970152821433173901 19599219738807308037440213)
                ·
                  refine ⟨459356712628296282127505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19599219738807308037440213 459356712628296282127505)
                  ·
                    rfl

theorem cell22_4025673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_4025673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025673 prefixEnd_4025673 := by exact prefixLift 4025673
  have htrace : WordTrace (prefixWord ++ tailWord_4025673) baseStart_4025673 baseEnd_4025673 := by
    simpa [prefixWord, tailWord_4025673, baseEnd_4025673] using wordTrace_append hprefix tailTrace_4025673
  have hstable : (prefixWord ++ tailWord_4025673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025673).length < 2 ^ (prefixWord ++ tailWord_4025673).sum := by decide
  have hdescent : baseEnd_4025673 < baseStart_4025673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025690 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_4025690 : Nat := 118140960795 + 4025690 * 2 ^ 59
def prefixEnd_4025690 : Nat := 4983230072969 + 3 ^ 40 * 4025690 * 2
def baseEnd_4025690 : Nat := 459358652444102156235821

theorem tailTrace_4025690 : CollatzResearch.WordTrace tailWord_4025690 prefixEnd_4025690 459358652444102156235821 := by
  unfold tailWord_4025690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36707244196405034489950631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97885984523746758639868349 36707244196405034489950631)
  ·
    refine ⟨55060866294607551734925947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36707244196405034489950631 55060866294607551734925947)
    ·
      refine ⟨82591299441911327602388921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55060866294607551734925947 82591299441911327602388921)
      ·
        refine ⟨61943474581433495701791691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82591299441911327602388921 61943474581433495701791691)
        ·
          refine ⟨92915211872150243552687537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61943474581433495701791691 92915211872150243552687537)
          ·
            refine ⟨69686408904112682664515653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92915211872150243552687537 69686408904112682664515653)
            ·
              refine ⟨13066201669521127999596685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69686408904112682664515653 13066201669521127999596685)
              ·
                refine ⟨4899825626070422999848757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13066201669521127999596685 4899825626070422999848757)
                ·
                  refine ⟨459358652444102156235821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899825626070422999848757 459358652444102156235821)
                  ·
                    rfl

theorem cell22_4025690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_4025690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025690 prefixEnd_4025690 := by exact prefixLift 4025690
  have htrace : WordTrace (prefixWord ++ tailWord_4025690) baseStart_4025690 baseEnd_4025690 := by
    simpa [prefixWord, tailWord_4025690, baseEnd_4025690] using wordTrace_append hprefix tailTrace_4025690
  have hstable : (prefixWord ++ tailWord_4025690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025690).length < 2 ^ (prefixWord ++ tailWord_4025690).sum := by decide
  have hdescent : baseEnd_4025690 < baseStart_4025690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025735 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 6]
def baseStart_4025735 : Nat := 118140960795 + 4025735 * 2 ^ 59
def prefixEnd_4025735 : Nat := 4983230072969 + 3 ^ 40 * 4025735 * 2
def baseEnd_4025735 : Nat := 459363787250647117110775

theorem tailTrace_4025735 : CollatzResearch.WordTrace tailWord_4025735 prefixEnd_4025735 459363787250647117110775 := by
  unfold tailWord_4025735
  simp only [CollatzResearch.WordTrace]
  refine ⟨146830618070457110645190659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97887078713638073763460439 146830618070457110645190659)
  ·
    refine ⟨220245927105685665967785989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146830618070457110645190659 220245927105685665967785989)
    ·
      refine ⟨41296111332316062368959873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220245927105685665967785989 41296111332316062368959873)
      ·
        refine ⟨30972083499237046776719905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41296111332316062368959873 30972083499237046776719905)
        ·
          refine ⟨23229062624427785082539929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30972083499237046776719905 23229062624427785082539929)
          ·
            refine ⟨17421796968320838811904947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23229062624427785082539929 17421796968320838811904947)
            ·
              refine ⟨26132695452481258217857421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17421796968320838811904947 26132695452481258217857421)
              ·
                refine ⟨9799760794680471831696533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26132695452481258217857421 9799760794680471831696533)
                ·
                  refine ⟨459363787250647117110775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9799760794680471831696533 459363787250647117110775)
                  ·
                    rfl

theorem cell22_4025735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 6].length) (baseStart_4025735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025735 prefixEnd_4025735 := by exact prefixLift 4025735
  have htrace : WordTrace (prefixWord ++ tailWord_4025735) baseStart_4025735 baseEnd_4025735 := by
    simpa [prefixWord, tailWord_4025735, baseEnd_4025735] using wordTrace_append hprefix tailTrace_4025735
  have hstable : (prefixWord ++ tailWord_4025735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025735).length < 2 ^ (prefixWord ++ tailWord_4025735).sum := by decide
  have hdescent : baseEnd_4025735 < baseStart_4025735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025767 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4025767 : Nat := 118140960795 + 4025767 * 2 ^ 59
def prefixEnd_4025767 : Nat := 4983230072969 + 3 ^ 40 * 4025767 * 2
def baseEnd_4025767 : Nat := 1378102316005903934532227

theorem tailTrace_4025767 : CollatzResearch.WordTrace tailWord_4025767 prefixEnd_4025767 1378102316005903934532227 := by
  unfold tailWord_4025767
  simp only [CollatzResearch.WordTrace]
  refine ⟨146831785206341180110355555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97887856804227453406903703 146831785206341180110355555)
  ·
    refine ⟨220247677809511770165533333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146831785206341180110355555 220247677809511770165533333)
    ·
      refine ⟨10324109897320864226509375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220247677809511770165533333 10324109897320864226509375)
      ·
        refine ⟨15486164845981296339764063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10324109897320864226509375 15486164845981296339764063)
        ·
          refine ⟨23229247268971944509646095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15486164845981296339764063 23229247268971944509646095)
          ·
            refine ⟨34843870903457916764469143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23229247268971944509646095 34843870903457916764469143)
            ·
              refine ⟨52265806355186875146703715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34843870903457916764469143 52265806355186875146703715)
              ·
                refine ⟨78398709532780312720055573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52265806355186875146703715 78398709532780312720055573)
                ·
                  refine ⟨3674939509349077158752605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78398709532780312720055573 3674939509349077158752605)
                  ·
                    refine ⟨1378102316005903934532227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3674939509349077158752605 1378102316005903934532227)
                    ·
                      rfl

theorem cell22_4025767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4025767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025767 prefixEnd_4025767 := by exact prefixLift 4025767
  have htrace : WordTrace (prefixWord ++ tailWord_4025767) baseStart_4025767 baseEnd_4025767 := by
    simpa [prefixWord, tailWord_4025767, baseEnd_4025767] using wordTrace_append hprefix tailTrace_4025767
  have hstable : (prefixWord ++ tailWord_4025767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025767).length < 2 ^ (prefixWord ++ tailWord_4025767).sum := by decide
  have hdescent : baseEnd_4025767 < baseStart_4025767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025889 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_4025889 : Nat := 118140960795 + 4025889 * 2 ^ 59
def prefixEnd_4025889 : Nat := 4983230072969 + 3 ^ 40 * 4025889 * 2
def baseEnd_4025889 : Nat := 1378144079099136282981853

theorem tailTrace_4025889 : CollatzResearch.WordTrace tailWord_4025889 prefixEnd_4025889 1378144079099136282981853 := by
  unfold tailWord_4025889
  simp only [CollatzResearch.WordTrace]
  refine ⟨146836234911899194946296721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97890823274599463297531147 146836234911899194946296721)
  ·
    refine ⟨110127176183924396209722541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146836234911899194946296721 110127176183924396209722541)
    ·
      refine ⟨41297691068971648578645953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110127176183924396209722541 41297691068971648578645953)
      ·
        refine ⟨30973268301728736433984465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41297691068971648578645953 30973268301728736433984465)
        ·
          refine ⟨23229951226296552325488349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30973268301728736433984465 23229951226296552325488349)
          ·
            refine ⟨8711231709861207122058131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23229951226296552325488349 8711231709861207122058131)
            ·
              refine ⟨13066847564791810683087197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711231709861207122058131 13066847564791810683087197)
              ·
                refine ⟨4900067836796929006157699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13066847564791810683087197 4900067836796929006157699)
                ·
                  refine ⟨7350101755195393509236549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900067836796929006157699 7350101755195393509236549)
                  ·
                    refine ⟨1378144079099136282981853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7350101755195393509236549 1378144079099136282981853)
                    ·
                      rfl

theorem cell22_4025889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_4025889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025889 prefixEnd_4025889 := by exact prefixLift 4025889
  have htrace : WordTrace (prefixWord ++ tailWord_4025889) baseStart_4025889 baseEnd_4025889 := by
    simpa [prefixWord, tailWord_4025889, baseEnd_4025889] using wordTrace_append hprefix tailTrace_4025889
  have hstable : (prefixWord ++ tailWord_4025889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025889).length < 2 ^ (prefixWord ++ tailWord_4025889).sum := by decide
  have hdescent : baseEnd_4025889 < baseStart_4025889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025919 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 1, 5]
def baseStart_4025919 : Nat := 118140960795 + 4025919 * 2 ^ 59
def prefixEnd_4025919 : Nat := 4983230072969 + 3 ^ 40 * 4025919 * 2
def baseEnd_4025919 : Nat := 1378154348712226204731761

theorem tailTrace_4025919 : CollatzResearch.WordTrace tailWord_4025919 prefixEnd_4025919 1378154348712226204731761 := by
  unfold tailWord_4025919
  simp only [CollatzResearch.WordTrace]
  refine ⟨146837329101790510069888811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97891552734527006713259207 146837329101790510069888811)
  ·
    refine ⟨220255993652685765104833217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146837329101790510069888811 220255993652685765104833217)
    ·
      refine ⟨165191995239514323828624913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220255993652685765104833217 165191995239514323828624913)
      ·
        refine ⟨123893996429635742871468685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165191995239514323828624913 123893996429635742871468685)
        ·
          refine ⟨46460248661113403576800757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123893996429635742871468685 46460248661113403576800757)
          ·
            refine ⟨4355648311979381585325071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46460248661113403576800757 4355648311979381585325071)
            ·
              refine ⟨6533472467969072377987607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355648311979381585325071 6533472467969072377987607)
              ·
                refine ⟨9800208701953608566981411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533472467969072377987607 9800208701953608566981411)
                ·
                  refine ⟨14700313052930412850472117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800208701953608566981411 14700313052930412850472117)
                  ·
                    refine ⟨1378154348712226204731761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14700313052930412850472117 1378154348712226204731761)
                    ·
                      rfl

theorem cell22_4025919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_4025919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025919 prefixEnd_4025919 := by exact prefixLift 4025919
  have htrace : WordTrace (prefixWord ++ tailWord_4025919) baseStart_4025919 baseEnd_4025919 := by
    simpa [prefixWord, tailWord_4025919, baseEnd_4025919] using wordTrace_append hprefix tailTrace_4025919
  have hstable : (prefixWord ++ tailWord_4025919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025919).length < 2 ^ (prefixWord ++ tailWord_4025919).sum := by decide
  have hdescent : baseEnd_4025919 < baseStart_4025919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4025932 : List Nat := [2, 2, 1, 3, 1, 4, 1, 8]
def baseStart_4025932 : Nat := 118140960795 + 4025932 * 2 ^ 59
def prefixEnd_4025932 : Nat := 4983230072969 + 3 ^ 40 * 4025932 * 2
def baseEnd_4025932 : Nat := 153128755430877611572969

theorem tailTrace_4025932 : CollatzResearch.WordTrace tailWord_4025932 prefixEnd_4025932 153128755430877611572969 := by
  unfold tailWord_4025932
  simp only [CollatzResearch.WordTrace]
  refine ⟨73418901625371706645056025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97891868833828942193408033 73418901625371706645056025)
  ·
    refine ⟨55064176219028779983792019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73418901625371706645056025 55064176219028779983792019)
    ·
      refine ⟨82596264328543169975688029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55064176219028779983792019 82596264328543169975688029)
      ·
        refine ⟨30973599123203688740883011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82596264328543169975688029 30973599123203688740883011)
        ·
          refine ⟨46460398684805533111324517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30973599123203688740883011 46460398684805533111324517)
          ·
            refine ⟨8711324753401037458373347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46460398684805533111324517 8711324753401037458373347)
            ·
              refine ⟨13066987130101556187560021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711324753401037458373347 13066987130101556187560021)
              ·
                refine ⟨153128755430877611572969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13066987130101556187560021 153128755430877611572969)
                ·
                  rfl

theorem cell22_4025932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_4025932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4025932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4025932 prefixEnd_4025932 := by exact prefixLift 4025932
  have htrace : WordTrace (prefixWord ++ tailWord_4025932) baseStart_4025932 baseEnd_4025932 := by
    simpa [prefixWord, tailWord_4025932, baseEnd_4025932] using wordTrace_append hprefix tailTrace_4025932
  have hstable : (prefixWord ++ tailWord_4025932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4025932).length < 2 ^ (prefixWord ++ tailWord_4025932).sum := by decide
  have hdescent : baseEnd_4025932 < baseStart_4025932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4025932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026015 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 1, 3]
def baseStart_4026015 : Nat := 118140960795 + 4026015 * 2 ^ 59
def prefixEnd_4026015 : Nat := 4983230072969 + 3 ^ 40 * 4026015 * 2
def baseEnd_4026015 : Nat := 1378187211474113954331467

theorem tailTrace_4026015 : CollatzResearch.WordTrace tailWord_4026015 prefixEnd_4026015 1378187211474113954331467 := by
  unfold tailWord_4026015
  simp only [CollatzResearch.WordTrace]
  refine ⟨146840830509442718465383499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97893887006295145643588999 146840830509442718465383499)
  ·
    refine ⟨220261245764164077698075249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146840830509442718465383499 220261245764164077698075249)
    ·
      refine ⟨165195934323123058273556437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220261245764164077698075249 165195934323123058273556437)
      ·
        refine ⟨3871779710698196678286479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 165195934323123058273556437 3871779710698196678286479)
        ·
          refine ⟨5807669566047295017429719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871779710698196678286479 5807669566047295017429719)
          ·
            refine ⟨8711504349070942526144579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807669566047295017429719 8711504349070942526144579)
            ·
              refine ⟨13067256523606413789216869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711504349070942526144579 13067256523606413789216869)
              ·
                refine ⟨2450110598176202585478163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13067256523606413789216869 2450110598176202585478163)
                ·
                  refine ⟨3675165897264303878217245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450110598176202585478163 3675165897264303878217245)
                  ·
                    refine ⟨1378187211474113954331467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675165897264303878217245 1378187211474113954331467)
                    ·
                      rfl

theorem cell22_4026015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_4026015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026015 prefixEnd_4026015 := by exact prefixLift 4026015
  have htrace : WordTrace (prefixWord ++ tailWord_4026015) baseStart_4026015 baseEnd_4026015 := by
    simpa [prefixWord, tailWord_4026015, baseEnd_4026015] using wordTrace_append hprefix tailTrace_4026015
  have hstable : (prefixWord ++ tailWord_4026015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026015).length < 2 ^ (prefixWord ++ tailWord_4026015).sum := by decide
  have hdescent : baseEnd_4026015 < baseStart_4026015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026039 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 6]
def baseStart_4026039 : Nat := 118140960795 + 4026039 * 2 ^ 59
def prefixEnd_4026039 : Nat := 4983230072969 + 3 ^ 40 * 4026039 * 2
def baseEnd_4026039 : Nat := 459398475721528630577131

theorem tailTrace_4026039 : CollatzResearch.WordTrace tailWord_4026039 prefixEnd_4026039 459398475721528630577131 := by
  unfold tailWord_4026039
  simp only [CollatzResearch.WordTrace]
  refine ⟨146841705861355770564257171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97894470574237180376171447 146841705861355770564257171)
  ·
    refine ⟨220262558792033655846385757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146841705861355770564257171 220262558792033655846385757)
    ·
      refine ⟨82598459547012620942394659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220262558792033655846385757 82598459547012620942394659)
      ·
        refine ⟨123897689320518931413591989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82598459547012620942394659 123897689320518931413591989)
        ·
          refine ⟨11615408373798649820024249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123897689320518931413591989 11615408373798649820024249)
          ·
            refine ⟨8711556280348987365018187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11615408373798649820024249 8711556280348987365018187)
            ·
              refine ⟨13067334420523481047527281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711556280348987365018187 13067334420523481047527281)
              ·
                refine ⟨9800500815392610785645461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13067334420523481047527281 9800500815392610785645461)
                ·
                  refine ⟨459398475721528630577131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9800500815392610785645461 459398475721528630577131)
                  ·
                    rfl

theorem cell22_4026039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 6].length) (baseStart_4026039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026039 prefixEnd_4026039 := by exact prefixLift 4026039
  have htrace : WordTrace (prefixWord ++ tailWord_4026039) baseStart_4026039 baseEnd_4026039 := by
    simpa [prefixWord, tailWord_4026039, baseEnd_4026039] using wordTrace_append hprefix tailTrace_4026039
  have hstable : (prefixWord ++ tailWord_4026039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026039).length < 2 ^ (prefixWord ++ tailWord_4026039).sum := by decide
  have hdescent : baseEnd_4026039 < baseStart_4026039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026056 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 4]
def baseStart_4026056 : Nat := 118140960795 + 4026056 * 2 ^ 59
def prefixEnd_4026056 : Nat := 4983230072969 + 3 ^ 40 * 4026056 * 2
def baseEnd_4026056 : Nat := 459400415537334504685447

theorem tailTrace_4026056 : CollatzResearch.WordTrace tailWord_4026056 prefixEnd_4026056 459400415537334504685447 := by
  unfold tailWord_4026056
  simp only [CollatzResearch.WordTrace]
  refine ⟨73421162951147091233813011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97894883934862788311750681 73421162951147091233813011)
  ·
    refine ⟨110131744426720636850719517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73421162951147091233813011 110131744426720636850719517)
    ·
      refine ⟨41299404160020238819019819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110131744426720636850719517 41299404160020238819019819)
      ·
        refine ⟨61949106240030358228529729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41299404160020238819019819 61949106240030358228529729)
        ·
          refine ⟨46461829680022768671397297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61949106240030358228529729 46461829680022768671397297)
          ·
            refine ⟨34846372260017076503547973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46461829680022768671397297 34846372260017076503547973)
            ·
              refine ⟨6533694798753201844415245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34846372260017076503547973 6533694798753201844415245)
              ·
                refine ⟨2450135549532450691655717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6533694798753201844415245 2450135549532450691655717)
                ·
                  refine ⟨459400415537334504685447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2450135549532450691655717 459400415537334504685447)
                  ·
                    rfl

theorem cell22_4026056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_4026056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026056 prefixEnd_4026056 := by exact prefixLift 4026056
  have htrace : WordTrace (prefixWord ++ tailWord_4026056) baseStart_4026056 baseEnd_4026056 := by
    simpa [prefixWord, tailWord_4026056, baseEnd_4026056] using wordTrace_append hprefix tailTrace_4026056
  have hstable : (prefixWord ++ tailWord_4026056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026056).length < 2 ^ (prefixWord ++ tailWord_4026056).sum := by decide
  have hdescent : baseEnd_4026056 < baseStart_4026056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026129 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 5]
def baseStart_4026129 : Nat := 118140960795 + 4026129 * 2 ^ 59
def prefixEnd_4026129 : Nat := 4983230072969 + 3 ^ 40 * 4026129 * 2
def baseEnd_4026129 : Nat := 459408745334618552327039

theorem tailTrace_4026129 : CollatzResearch.WordTrace tailWord_4026129 prefixEnd_4026129 459408745334618552327039 := by
  unfold tailWord_4026129
  simp only [CollatzResearch.WordTrace]
  refine ⟨146844988431029715935033441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97896658954019810623355627 146844988431029715935033441)
  ·
    refine ⟨110133741323272286951275081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146844988431029715935033441 110133741323272286951275081)
    ·
      refine ⟨82600305992454215213456311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110133741323272286951275081 82600305992454215213456311)
      ·
        refine ⟨123900458988681322820184467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82600305992454215213456311 123900458988681322820184467)
        ·
          refine ⟨185850688483021984230276701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123900458988681322820184467 185850688483021984230276701)
          ·
            refine ⟨69694008181133244086353763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185850688483021984230276701 69694008181133244086353763)
            ·
              refine ⟨104541012271699866129530645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69694008181133244086353763 104541012271699866129530645)
              ·
                refine ⟨4900359950235931224821749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104541012271699866129530645 4900359950235931224821749)
                ·
                  refine ⟨459408745334618552327039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4900359950235931224821749 459408745334618552327039)
                  ·
                    rfl

theorem cell22_4026129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_4026129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026129 prefixEnd_4026129 := by exact prefixLift 4026129
  have htrace : WordTrace (prefixWord ++ tailWord_4026129) baseStart_4026129 baseEnd_4026129 := by
    simpa [prefixWord, tailWord_4026129, baseEnd_4026129] using wordTrace_append hprefix tailTrace_4026129
  have hstable : (prefixWord ++ tailWord_4026129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026129).length < 2 ^ (prefixWord ++ tailWord_4026129).sum := by decide
  have hdescent : baseEnd_4026129 < baseStart_4026129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026133 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_4026133 : Nat := 118140960795 + 4026133 * 2 ^ 59
def prefixEnd_4026133 : Nat := 4983230072969 + 3 ^ 40 * 4026133 * 2
def baseEnd_4026133 : Nat := 1378227605285600979881105

theorem tailTrace_4026133 : CollatzResearch.WordTrace tailWord_4026133 prefixEnd_4026133 1378227605285600979881105 := by
  unfold tailWord_4026133
  simp only [CollatzResearch.WordTrace]
  refine ⟨146845134323015224618179053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97896756215343483078786035 146845134323015224618179053)
  ·
    refine ⟨55066925371130709231817145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146845134323015224618179053 55066925371130709231817145)
    ·
      refine ⟨41300194028348031923862859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55066925371130709231817145 41300194028348031923862859)
      ·
        refine ⟨61950291042522047885794289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41300194028348031923862859 61950291042522047885794289)
        ·
          refine ⟨46462718281891535914345717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61950291042522047885794289 46462718281891535914345717)
          ·
            refine ⟨4355879838927331491969911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46462718281891535914345717 4355879838927331491969911)
            ·
              refine ⟨6533819758390997237954867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355879838927331491969911 6533819758390997237954867)
              ·
                refine ⟨9800729637586495856932301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533819758390997237954867 9800729637586495856932301)
                ·
                  refine ⟨3675273614094935946349613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9800729637586495856932301 3675273614094935946349613)
                  ·
                    refine ⟨1378227605285600979881105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675273614094935946349613 1378227605285600979881105)
                    ·
                      rfl

theorem cell22_4026133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_4026133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026133 prefixEnd_4026133 := by exact prefixLift 4026133
  have htrace : WordTrace (prefixWord ++ tailWord_4026133) baseStart_4026133 baseEnd_4026133 := by
    simpa [prefixWord, tailWord_4026133, baseEnd_4026133] using wordTrace_append hprefix tailTrace_4026133
  have hstable : (prefixWord ++ tailWord_4026133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026133).length < 2 ^ (prefixWord ++ tailWord_4026133).sum := by decide
  have hdescent : baseEnd_4026133 < baseStart_4026133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026144 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_4026144 : Nat := 118140960795 + 4026144 * 2 ^ 59
def prefixEnd_4026144 : Nat := 4983230072969 + 3 ^ 40 * 4026144 * 2
def baseEnd_4026144 : Nat := 1378231370810400617856071

theorem tailTrace_4026144 : CollatzResearch.WordTrace tailWord_4026144 prefixEnd_4026144 1378231370810400617856071 := by
  unfold tailWord_4026144
  simp only [CollatzResearch.WordTrace]
  refine ⟨73422767762987686748414743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97897023683983582331219657 73422767762987686748414743)
  ·
    refine ⟨110134151644481530122622115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73422767762987686748414743 110134151644481530122622115)
    ·
      refine ⟨165201227466722295183933173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110134151644481530122622115 165201227466722295183933173)
      ·
        refine ⟨15487615075005215173493735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165201227466722295183933173 15487615075005215173493735)
        ·
          refine ⟨23231422612507822760240603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15487615075005215173493735 23231422612507822760240603)
          ·
            refine ⟨34847133918761734140360905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23231422612507822760240603 34847133918761734140360905)
            ·
              refine ⟨26135350439071300605270679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34847133918761734140360905 26135350439071300605270679)
              ·
                refine ⟨39203025658606950907906019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26135350439071300605270679 39203025658606950907906019)
                ·
                  refine ⟨58804538487910426361859029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39203025658606950907906019 58804538487910426361859029)
                  ·
                    refine ⟨1378231370810400617856071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58804538487910426361859029 1378231370810400617856071)
                    ·
                      rfl

theorem cell22_4026144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_4026144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026144 prefixEnd_4026144 := by exact prefixLift 4026144
  have htrace : WordTrace (prefixWord ++ tailWord_4026144) baseStart_4026144 baseEnd_4026144 := by
    simpa [prefixWord, tailWord_4026144, baseEnd_4026144] using wordTrace_append hprefix tailTrace_4026144
  have hstable : (prefixWord ++ tailWord_4026144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026144).length < 2 ^ (prefixWord ++ tailWord_4026144).sum := by decide
  have hdescent : baseEnd_4026144 < baseStart_4026144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026146 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_4026146 : Nat := 118140960795 + 4026146 * 2 ^ 59
def prefixEnd_4026146 : Nat := 4983230072969 + 3 ^ 40 * 4026146 * 2
def baseEnd_4026146 : Nat := 459410685150424426435355

theorem tailTrace_4026146 : CollatzResearch.WordTrace tailWord_4026146 prefixEnd_4026146 459410685150424426435355 := by
  unfold tailWord_4026146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36711402117992031959600573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97897072314645418558934861 36711402117992031959600573)
  ·
    refine ⟨13766775794247011984850215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36711402117992031959600573 13766775794247011984850215)
    ·
      refine ⟨20650163691370517977275323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13766775794247011984850215 20650163691370517977275323)
      ·
        refine ⟨30975245537055776965912985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20650163691370517977275323 30975245537055776965912985)
        ·
          refine ⟨23231434152791832724434739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30975245537055776965912985 23231434152791832724434739)
          ·
            refine ⟨34847151229187749086652109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23231434152791832724434739 34847151229187749086652109)
            ·
              refine ⟨13067681710945405907494541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34847151229187749086652109 13067681710945405907494541)
              ·
                refine ⟨4900380641604527215310453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13067681710945405907494541 4900380641604527215310453)
                ·
                  refine ⟨459410685150424426435355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4900380641604527215310453 459410685150424426435355)
                  ·
                    rfl

theorem cell22_4026146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_4026146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026146 prefixEnd_4026146 := by exact prefixLift 4026146
  have htrace : WordTrace (prefixWord ++ tailWord_4026146) baseStart_4026146 baseEnd_4026146 := by
    simpa [prefixWord, tailWord_4026146, baseEnd_4026146] using wordTrace_append hprefix tailTrace_4026146
  have hstable : (prefixWord ++ tailWord_4026146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026146).length < 2 ^ (prefixWord ++ tailWord_4026146).sum := by decide
  have hdescent : baseEnd_4026146 < baseStart_4026146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026159 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 3, 4]
def baseStart_4026159 : Nat := 118140960795 + 4026159 * 2 ^ 59
def prefixEnd_4026159 : Nat := 4983230072969 + 3 ^ 40 * 4026159 * 2
def baseEnd_4026159 : Nat := 1378236505616945578731025

theorem tailTrace_4026159 : CollatzResearch.WordTrace tailWord_4026159 prefixEnd_4026159 1378236505616945578731025 := by
  unfold tailWord_4026159
  simp only [CollatzResearch.WordTrace]
  refine ⟨146846082620921031058625531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97897388413947354039083687 146846082620921031058625531)
  ·
    refine ⟨220269123931381546587938297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146846082620921031058625531 220269123931381546587938297)
    ·
      refine ⟨165201842948536159940953723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220269123931381546587938297 165201842948536159940953723)
      ·
        refine ⟨247802764422804239911430585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165201842948536159940953723 247802764422804239911430585)
        ·
          refine ⟨185852073317103179933572939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247802764422804239911430585 185852073317103179933572939)
          ·
            refine ⟨278778109975654769900359409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185852073317103179933572939 278778109975654769900359409)
            ·
              refine ⟨209083582481741077425269557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278778109975654769900359409 209083582481741077425269557)
              ·
                refine ⟨19601585857663226008619021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209083582481741077425269557 19601585857663226008619021)
                ·
                  refine ⟨7350594696623709753232133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19601585857663226008619021 7350594696623709753232133)
                  ·
                    refine ⟨1378236505616945578731025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7350594696623709753232133 1378236505616945578731025)
                    ·
                      rfl

theorem cell22_4026159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_4026159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026159 prefixEnd_4026159 := by exact prefixLift 4026159
  have htrace : WordTrace (prefixWord ++ tailWord_4026159) baseStart_4026159 baseEnd_4026159 := by
    simpa [prefixWord, tailWord_4026159, baseEnd_4026159] using wordTrace_append hprefix tailTrace_4026159
  have hstable : (prefixWord ++ tailWord_4026159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026159).length < 2 ^ (prefixWord ++ tailWord_4026159).sum := by decide
  have hdescent : baseEnd_4026159 < baseStart_4026159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026270 : List Nat := [4, 3, 1, 3, 1, 1, 1, 8]
def baseStart_4026270 : Nat := 118140960795 + 4026270 * 2 ^ 59
def prefixEnd_4026270 : Nat := 4983230072969 + 3 ^ 40 * 4026270 * 2
def baseEnd_4026270 : Nat := 153141611465042032133965

theorem tailTrace_4026270 : CollatzResearch.WordTrace tailWord_4026270 prefixEnd_4026270 153141611465042032133965 := by
  unfold tailWord_4026270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356266390439862126989533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97900087415679264677277509 18356266390439862126989533)
  ·
    refine ⟨6883599896414948297621075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18356266390439862126989533 6883599896414948297621075)
    ·
      refine ⟨10325399844622422446431613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883599896414948297621075 10325399844622422446431613)
      ·
        refine ⟨3872024941733408417411855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10325399844622422446431613 3872024941733408417411855)
        ·
          refine ⟨5808037412600112626117783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872024941733408417411855 5808037412600112626117783)
          ·
            refine ⟨8712056118900168939176675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808037412600112626117783 8712056118900168939176675)
            ·
              refine ⟨13068084178350253408765013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712056118900168939176675 13068084178350253408765013)
              ·
                refine ⟨153141611465042032133965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13068084178350253408765013 153141611465042032133965)
                ·
                  rfl

theorem cell22_4026270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_4026270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026270 prefixEnd_4026270 := by exact prefixLift 4026270
  have htrace : WordTrace (prefixWord ++ tailWord_4026270) baseStart_4026270 baseEnd_4026270 := by
    simpa [prefixWord, tailWord_4026270, baseEnd_4026270] using wordTrace_append hprefix tailTrace_4026270
  have hstable : (prefixWord ++ tailWord_4026270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026270).length < 2 ^ (prefixWord ++ tailWord_4026270).sum := by decide
  have hdescent : baseEnd_4026270 < baseStart_4026270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026311 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 3, 4]
def baseStart_4026311 : Nat := 118140960795 + 4026311 * 2 ^ 59
def prefixEnd_4026311 : Nat := 4983230072969 + 3 ^ 40 * 4026311 * 2
def baseEnd_4026311 : Nat := 1378288538323267848930559

theorem tailTrace_4026311 : CollatzResearch.WordTrace tailWord_4026311 prefixEnd_4026311 1378288538323267848930559 := by
  unfold tailWord_4026311
  simp only [CollatzResearch.WordTrace]
  refine ⟨146851626516370361018158787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97901084344246907345439191 146851626516370361018158787)
  ·
    refine ⟨220277439774555541527238181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146851626516370361018158787 220277439774555541527238181)
    ·
      refine ⟨41302019957729164036357159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220277439774555541527238181 41302019957729164036357159)
      ·
        refine ⟨61953029936593746054535739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41302019957729164036357159 61953029936593746054535739)
        ·
          refine ⟨92929544904890619081803609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61953029936593746054535739 92929544904890619081803609)
          ·
            refine ⟨69697158678667964311352707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92929544904890619081803609 69697158678667964311352707)
            ·
              refine ⟨104545738018001946467029061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69697158678667964311352707 104545738018001946467029061)
              ·
                refine ⟨19602325878375364962567949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104545738018001946467029061 19602325878375364962567949)
                ·
                  refine ⟨7350872204390761860962981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19602325878375364962567949 7350872204390761860962981)
                  ·
                    refine ⟨1378288538323267848930559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7350872204390761860962981 1378288538323267848930559)
                    ·
                      rfl

theorem cell22_4026311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_4026311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026311 prefixEnd_4026311 := by exact prefixLift 4026311
  have htrace : WordTrace (prefixWord ++ tailWord_4026311) baseStart_4026311 baseEnd_4026311 := by
    simpa [prefixWord, tailWord_4026311, baseEnd_4026311] using wordTrace_append hprefix tailTrace_4026311
  have hstable : (prefixWord ++ tailWord_4026311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026311).length < 2 ^ (prefixWord ++ tailWord_4026311).sum := by decide
  have hdescent : baseEnd_4026311 < baseStart_4026311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026360 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 4]
def baseStart_4026360 : Nat := 118140960795 + 4026360 * 2 ^ 59
def prefixEnd_4026360 : Nat := 4983230072969 + 3 ^ 40 * 4026360 * 2
def baseEnd_4026360 : Nat := 459435104008216018151803

theorem tailTrace_4026360 : CollatzResearch.WordTrace tailWord_4026360 prefixEnd_4026360 459435104008216018151803 := by
  unfold tailWord_4026360
  simp only [CollatzResearch.WordTrace]
  refine ⟨73426706846596421193346267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97902275795461894924461689 73426706846596421193346267)
  ·
    refine ⟨110140060269894631790019401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73426706846596421193346267 110140060269894631790019401)
    ·
      refine ⟨82605045202420973842514551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110140060269894631790019401 82605045202420973842514551)
      ·
        refine ⟨123907567803631460763771827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82605045202420973842514551 123907567803631460763771827)
        ·
          refine ⟨185861351705447191145657741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123907567803631460763771827 185861351705447191145657741)
          ·
            refine ⟨69698006889542696679621653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185861351705447191145657741 69698006889542696679621653)
            ·
              refine ⟨3267094072947313906857265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69698006889542696679621653 3267094072947313906857265)
              ·
                refine ⟨2450320554710485430142949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267094072947313906857265 2450320554710485430142949)
                ·
                  refine ⟨459435104008216018151803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2450320554710485430142949 459435104008216018151803)
                  ·
                    rfl

theorem cell22_4026360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_4026360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026360 prefixEnd_4026360 := by exact prefixLift 4026360
  have htrace : WordTrace (prefixWord ++ tailWord_4026360) baseStart_4026360 baseEnd_4026360 := by
    simpa [prefixWord, tailWord_4026360, baseEnd_4026360] using wordTrace_append hprefix tailTrace_4026360
  have hstable : (prefixWord ++ tailWord_4026360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026360).length < 2 ^ (prefixWord ++ tailWord_4026360).sum := by decide
  have hdescent : baseEnd_4026360 < baseStart_4026360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026375 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 2, 3]
def baseStart_4026375 : Nat := 118140960795 + 4026375 * 2 ^ 59
def prefixEnd_4026375 : Nat := 4983230072969 + 3 ^ 40 * 4026375 * 2
def baseEnd_4026375 : Nat := 1378310446831193015330363

theorem tailTrace_4026375 : CollatzResearch.WordTrace tailWord_4026375 prefixEnd_4026375 1378310446831193015330363 := by
  unfold tailWord_4026375
  simp only [CollatzResearch.WordTrace]
  refine ⟨146853960788138499948488579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97902640525425666632325719 146853960788138499948488579)
  ·
    refine ⟨220280941182207749922732869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146853960788138499948488579 220280941182207749922732869)
    ·
      refine ⟨41302676471663953110512413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220280941182207749922732869 41302676471663953110512413)
      ·
        refine ⟨15488503676873982416442155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41302676471663953110512413 15488503676873982416442155)
        ·
          refine ⟨23232755515310973624663233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15488503676873982416442155 23232755515310973624663233)
          ·
            refine ⟨17424566636483230218497425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23232755515310973624663233 17424566636483230218497425)
            ·
              refine ⟨13068424977362422663873069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17424566636483230218497425 13068424977362422663873069)
              ·
                refine ⟨4900659366510908498952401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13068424977362422663873069 4900659366510908498952401)
                ·
                  refine ⟨3675494524883181374214301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900659366510908498952401 3675494524883181374214301)
                  ·
                    refine ⟨1378310446831193015330363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675494524883181374214301 1378310446831193015330363)
                    ·
                      rfl

theorem cell22_4026375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_4026375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026375 prefixEnd_4026375 := by exact prefixLift 4026375
  have htrace : WordTrace (prefixWord ++ tailWord_4026375) baseStart_4026375 baseEnd_4026375 := by
    simpa [prefixWord, tailWord_4026375, baseEnd_4026375] using wordTrace_append hprefix tailTrace_4026375
  have hstable : (prefixWord ++ tailWord_4026375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026375).length < 2 ^ (prefixWord ++ tailWord_4026375).sum := by decide
  have hdescent : baseEnd_4026375 < baseStart_4026375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026403 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 5, 3]
def baseStart_4026403 : Nat := 118140960795 + 4026403 * 2 ^ 59
def prefixEnd_4026403 : Nat := 4983230072969 + 3 ^ 40 * 4026403 * 2
def baseEnd_4026403 : Nat := 1378320031803410275630277

theorem tailTrace_4026403 : CollatzResearch.WordTrace tailWord_4026403 prefixEnd_4026403 1378320031803410275630277 := by
  unfold tailWord_4026403
  simp only [CollatzResearch.WordTrace]
  refine ⟨146854982032037060730507863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97903321354691373820338575 146854982032037060730507863)
  ·
    refine ⟨220282473048055591095761795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146854982032037060730507863 220282473048055591095761795)
    ·
      refine ⟨330423709572083386643642693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220282473048055591095761795 330423709572083386643642693)
      ·
        refine ⟨61954445544765634995683005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330423709572083386643642693 61954445544765634995683005)
        ·
          refine ⟨23232917079287113123381127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61954445544765634995683005 23232917079287113123381127)
          ·
            refine ⟨34849375618930669685071691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23232917079287113123381127 34849375618930669685071691)
            ·
              refine ⟨52274063428396004527607537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34849375618930669685071691 52274063428396004527607537)
              ·
                refine ⟨39205547571297003395705653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52274063428396004527607537 39205547571297003395705653)
                ·
                  refine ⟨3675520084809094068347405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39205547571297003395705653 3675520084809094068347405)
                  ·
                    refine ⟨1378320031803410275630277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675520084809094068347405 1378320031803410275630277)
                    ·
                      rfl

theorem cell22_4026403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 3].length) (baseStart_4026403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026403 prefixEnd_4026403 := by exact prefixLift 4026403
  have htrace : WordTrace (prefixWord ++ tailWord_4026403) baseStart_4026403 baseEnd_4026403 := by
    simpa [prefixWord, tailWord_4026403, baseEnd_4026403] using wordTrace_append hprefix tailTrace_4026403
  have hstable : (prefixWord ++ tailWord_4026403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026403).length < 2 ^ (prefixWord ++ tailWord_4026403).sum := by decide
  have hdescent : baseEnd_4026403 < baseStart_4026403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026518 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4026518 : Nat := 118140960795 + 4026518 * 2 ^ 59
def prefixEnd_4026518 : Nat := 4983230072969 + 3 ^ 40 * 4026518 * 2
def baseEnd_4026518 : Nat := 459453132884529436334975

theorem tailTrace_4026518 : CollatzResearch.WordTrace tailWord_4026518 prefixEnd_4026518 459453132884529436334975 := by
  unfold tailWord_4026518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178698526663777210684013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97906117617746956913962805 9178698526663777210684013)
  ·
    refine ⟨3442011947498916454006505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9178698526663777210684013 3442011947498916454006505)
    ·
      refine ⟨2581508960624187340504879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3442011947498916454006505 2581508960624187340504879)
      ·
        refine ⟨3872263440936281010757319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581508960624187340504879 3872263440936281010757319)
        ·
          refine ⟨5808395161404421516135979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872263440936281010757319 5808395161404421516135979)
          ·
            refine ⟨8712592742106632274203969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808395161404421516135979 8712592742106632274203969)
            ·
              refine ⟨6534444556579974205652977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8712592742106632274203969 6534444556579974205652977)
              ·
                refine ⟨4900833417434980654239733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534444556579974205652977 4900833417434980654239733)
                ·
                  refine ⟨459453132884529436334975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4900833417434980654239733 459453132884529436334975)
                  ·
                    rfl

theorem cell22_4026518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4026518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026518 prefixEnd_4026518 := by exact prefixLift 4026518
  have htrace : WordTrace (prefixWord ++ tailWord_4026518) baseStart_4026518 baseEnd_4026518 := by
    simpa [prefixWord, tailWord_4026518, baseEnd_4026518] using wordTrace_append hprefix tailTrace_4026518
  have hstable : (prefixWord ++ tailWord_4026518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026518).length < 2 ^ (prefixWord ++ tailWord_4026518).sum := by decide
  have hdescent : baseEnd_4026518 < baseStart_4026518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026525 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4026525 : Nat := 118140960795 + 4026525 * 2 ^ 59
def prefixEnd_4026525 : Nat := 4983230072969 + 3 ^ 40 * 4026525 * 2
def baseEnd_4026525 : Nat := 1378361794896642624079903

theorem tailTrace_4026525 : CollatzResearch.WordTrace tailWord_4026525 prefixEnd_4026525 1378361794896642624079903 := by
  unfold tailWord_4026525
  simp only [CollatzResearch.WordTrace]
  refine ⟨146859431737595075566449029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97906287825063383710966019 146859431737595075566449029)
  ·
    refine ⟨27536143450799076668709193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146859431737595075566449029 27536143450799076668709193)
    ·
      refine ⟨20652107588099307501531895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27536143450799076668709193 20652107588099307501531895)
      ·
        refine ⟨30978161382148961252297843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20652107588099307501531895 30978161382148961252297843)
        ·
          refine ⟨46467242073223441878446765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30978161382148961252297843 46467242073223441878446765)
          ·
            refine ⟨17425215777458790704417537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46467242073223441878446765 17425215777458790704417537)
            ·
              refine ⟨13068911833094093028313153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17425215777458790704417537 13068911833094093028313153)
              ·
                refine ⟨9801683874820569771234865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13068911833094093028313153 9801683874820569771234865)
                ·
                  refine ⟨7351262906115427328426149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9801683874820569771234865 7351262906115427328426149)
                  ·
                    refine ⟨1378361794896642624079903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351262906115427328426149 1378361794896642624079903)
                    ·
                      rfl

theorem cell22_4026525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4026525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026525 prefixEnd_4026525 := by exact prefixLift 4026525
  have htrace : WordTrace (prefixWord ++ tailWord_4026525) baseStart_4026525 baseEnd_4026525 := by
    simpa [prefixWord, tailWord_4026525, baseEnd_4026525] using wordTrace_append hprefix tailTrace_4026525
  have hstable : (prefixWord ++ tailWord_4026525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026525).length < 2 ^ (prefixWord ++ tailWord_4026525).sum := by decide
  have hdescent : baseEnd_4026525 < baseStart_4026525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026527 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 2, 3]
def baseStart_4026527 : Nat := 118140960795 + 4026527 * 2 ^ 59
def prefixEnd_4026527 : Nat := 4983230072969 + 3 ^ 40 * 4026527 * 2
def baseEnd_4026527 : Nat := 1378362479537515285529897

theorem tailTrace_4026527 : CollatzResearch.WordTrace tailWord_4026527 prefixEnd_4026527 1378362479537515285529897 := by
  unfold tailWord_4026527
  simp only [CollatzResearch.WordTrace]
  refine ⟨146859504683587829908021835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97906336455725219938681223 146859504683587829908021835)
  ·
    refine ⟨220289257025381744862032753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146859504683587829908021835 220289257025381744862032753)
    ·
      refine ⟨165216942769036308646524565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220289257025381744862032753 165216942769036308646524565)
      ·
        refine ⟨7744544192298576967805839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165216942769036308646524565 7744544192298576967805839)
        ·
          refine ⟨11616816288447865451708759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744544192298576967805839 11616816288447865451708759)
          ·
            refine ⟨17425224432671798177563139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616816288447865451708759 17425224432671798177563139)
            ·
              refine ⟨26137836649007697266344709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17425224432671798177563139 26137836649007697266344709)
              ·
                refine ⟨4900844371688943237439633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26137836649007697266344709 4900844371688943237439633)
                ·
                  refine ⟨3675633278766707428079725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900844371688943237439633 3675633278766707428079725)
                  ·
                    refine ⟨1378362479537515285529897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675633278766707428079725 1378362479537515285529897)
                    ·
                      rfl

theorem cell22_4026527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_4026527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026527 prefixEnd_4026527 := by exact prefixLift 4026527
  have htrace : WordTrace (prefixWord ++ tailWord_4026527) baseStart_4026527 baseEnd_4026527 := by
    simpa [prefixWord, tailWord_4026527, baseEnd_4026527] using wordTrace_append hprefix tailTrace_4026527
  have hstable : (prefixWord ++ tailWord_4026527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026527).length < 2 ^ (prefixWord ++ tailWord_4026527).sum := by decide
  have hdescent : baseEnd_4026527 < baseStart_4026527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026529 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 4]
def baseStart_4026529 : Nat := 118140960795 + 4026529 * 2 ^ 59
def prefixEnd_4026529 : Nat := 4983230072969 + 3 ^ 40 * 4026529 * 2
def baseEnd_4026529 : Nat := 459454388059462648993297

theorem tailTrace_4026529 : CollatzResearch.WordTrace tailWord_4026529 prefixEnd_4026529 459454388059462648993297 := by
  unfold tailWord_4026529
  simp only [CollatzResearch.WordTrace]
  refine ⟨146859577629580584249594641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97906385086387056166396427 146859577629580584249594641)
  ·
    refine ⟨110144683222185438187195981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146859577629580584249594641 110144683222185438187195981)
    ·
      refine ⟨41304256208319539320198493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110144683222185438187195981 41304256208319539320198493)
      ·
        refine ⟨15489096078119827245074435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41304256208319539320198493 15489096078119827245074435)
        ·
          refine ⟨23233644117179740867611653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15489096078119827245074435 23233644117179740867611653)
          ·
            refine ⟨4356308271971201412677185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23233644117179740867611653 4356308271971201412677185)
            ·
              refine ⟨3267231203978401059507889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356308271971201412677185 3267231203978401059507889)
              ·
                refine ⟨2450423402983800794630917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267231203978401059507889 2450423402983800794630917)
                ·
                  refine ⟨459454388059462648993297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2450423402983800794630917 459454388059462648993297)
                  ·
                    rfl

theorem cell22_4026529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_4026529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026529 prefixEnd_4026529 := by exact prefixLift 4026529
  have htrace : WordTrace (prefixWord ++ tailWord_4026529) baseStart_4026529 baseEnd_4026529 := by
    simpa [prefixWord, tailWord_4026529, baseEnd_4026529] using wordTrace_append hprefix tailTrace_4026529
  have hstable : (prefixWord ++ tailWord_4026529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026529).length < 2 ^ (prefixWord ++ tailWord_4026529).sum := by decide
  have hdescent : baseEnd_4026529 < baseStart_4026529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026553 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_4026553 : Nat := 118140960795 + 4026553 * 2 ^ 59
def prefixEnd_4026553 : Nat := 4983230072969 + 3 ^ 40 * 4026553 * 2
def baseEnd_4026553 : Nat := 1378371379868859884379817

theorem tailTrace_4026553 : CollatzResearch.WordTrace tailWord_4026553 prefixEnd_4026553 1378371379868859884379817 := by
  unfold tailWord_4026553
  simp only [CollatzResearch.WordTrace]
  refine ⟨146860452981493636348468313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97906968654329090898978875 146860452981493636348468313)
  ·
    refine ⟨110145339736120227261351235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146860452981493636348468313 110145339736120227261351235)
    ·
      refine ⟨165218009604180340892026853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110145339736120227261351235 165218009604180340892026853)
      ·
        refine ⟨30978376800783813917255035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165218009604180340892026853 30978376800783813917255035)
        ·
          refine ⟨46467565201175720875882553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30978376800783813917255035 46467565201175720875882553)
          ·
            refine ⟨34850673900881790656911915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46467565201175720875882553 34850673900881790656911915)
            ·
              refine ⟨52276010851322685985367873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34850673900881790656911915 52276010851322685985367873)
              ·
                refine ⟨39207008138492014489025905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52276010851322685985367873 39207008138492014489025905)
                ·
                  refine ⟨29405256103869010866769429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39207008138492014489025905 29405256103869010866769429)
                  ·
                    refine ⟨1378371379868859884379817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29405256103869010866769429 1378371379868859884379817)
                    ·
                      rfl

theorem cell22_4026553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_4026553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026553 prefixEnd_4026553 := by exact prefixLift 4026553
  have htrace : WordTrace (prefixWord ++ tailWord_4026553) baseStart_4026553 baseEnd_4026553 := by
    simpa [prefixWord, tailWord_4026553, baseEnd_4026553] using wordTrace_append hprefix tailTrace_4026553
  have hstable : (prefixWord ++ tailWord_4026553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026553).length < 2 ^ (prefixWord ++ tailWord_4026553).sum := by decide
  have hdescent : baseEnd_4026553 < baseStart_4026553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026555 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 3, 3]
def baseStart_4026555 : Nat := 118140960795 + 4026555 * 2 ^ 59
def prefixEnd_4026555 : Nat := 4983230072969 + 3 ^ 40 * 4026555 * 2
def baseEnd_4026555 : Nat := 1378372064509732545829811

theorem tailTrace_4026555 : CollatzResearch.WordTrace tailWord_4026555 prefixEnd_4026555 1378372064509732545829811 := by
  unfold tailWord_4026555
  simp only [CollatzResearch.WordTrace]
  refine ⟨146860525927486390690041119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97907017284990927126694079 146860525927486390690041119)
  ·
    refine ⟨220290788891229586035061679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146860525927486390690041119 220290788891229586035061679)
    ·
      refine ⟨330436183336844379052592519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220290788891229586035061679 330436183336844379052592519)
      ·
        refine ⟨495654275005266568578888779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330436183336844379052592519 495654275005266568578888779)
        ·
          refine ⟨743481412507899852868333169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495654275005266568578888779 743481412507899852868333169)
          ·
            refine ⟨557611059380924889651249877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743481412507899852868333169 557611059380924889651249877)
            ·
              refine ⟨13069009204240427101201169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 557611059380924889651249877 13069009204240427101201169)
              ·
                refine ⟨9801756903180320325900877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13069009204240427101201169 9801756903180320325900877)
                ·
                  refine ⟨3675658838692620122212829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9801756903180320325900877 3675658838692620122212829)
                  ·
                    refine ⟨1378372064509732545829811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675658838692620122212829 1378372064509732545829811)
                    ·
                      rfl

theorem cell22_4026555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 3].length) (baseStart_4026555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026555 prefixEnd_4026555 := by exact prefixLift 4026555
  have htrace : WordTrace (prefixWord ++ tailWord_4026555) baseStart_4026555 baseEnd_4026555 := by
    simpa [prefixWord, tailWord_4026555, baseEnd_4026555] using wordTrace_append hprefix tailTrace_4026555
  have hstable : (prefixWord ++ tailWord_4026555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026555).length < 2 ^ (prefixWord ++ tailWord_4026555).sum := by decide
  have hdescent : baseEnd_4026555 < baseStart_4026555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026568 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_4026568 : Nat := 118140960795 + 4026568 * 2 ^ 59
def prefixEnd_4026568 : Nat := 4983230072969 + 3 ^ 40 * 4026568 * 2
def baseEnd_4026568 : Nat := 459458838225134948418257

theorem tailTrace_4026568 : CollatzResearch.WordTrace tailWord_4026568 prefixEnd_4026568 459458838225134948418257 := by
  unfold tailWord_4026568
  simp only [CollatzResearch.WordTrace]
  refine ⟨73430500038219646955132179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97907333384292862606842905 73430500038219646955132179)
  ·
    refine ⟨110145750057329470432698269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73430500038219646955132179 110145750057329470432698269)
    ·
      refine ⟨41304656271498551412261851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110145750057329470432698269 41304656271498551412261851)
      ·
        refine ⟨61956984407247827118392777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41304656271498551412261851 61956984407247827118392777)
        ·
          refine ⟨46467738305435870338794583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61956984407247827118392777 46467738305435870338794583)
          ·
            refine ⟨69701607458153805508191875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46467738305435870338794583 69701607458153805508191875)
            ·
              refine ⟨104552411187230708262287813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69701607458153805508191875 104552411187230708262287813)
              ·
                refine ⟨19603577097605757799178965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104552411187230708262287813 19603577097605757799178965)
                ·
                  refine ⟨459458838225134948418257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19603577097605757799178965 459458838225134948418257)
                  ·
                    rfl

theorem cell22_4026568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_4026568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026568 prefixEnd_4026568 := by exact prefixLift 4026568
  have htrace : WordTrace (prefixWord ++ tailWord_4026568) baseStart_4026568 baseEnd_4026568 := by
    simpa [prefixWord, tailWord_4026568, baseEnd_4026568] using wordTrace_append hprefix tailTrace_4026568
  have hstable : (prefixWord ++ tailWord_4026568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026568).length < 2 ^ (prefixWord ++ tailWord_4026568).sum := by decide
  have hdescent : baseEnd_4026568 < baseStart_4026568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026585 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 5]
def baseStart_4026585 : Nat := 118140960795 + 4026585 * 2 ^ 59
def prefixEnd_4026585 : Nat := 4983230072969 + 3 ^ 40 * 4026585 * 2
def baseEnd_4026585 : Nat := 459460778040940822526573

theorem tailTrace_4026585 : CollatzResearch.WordTrace tailWord_4026585 prefixEnd_4026585 459460778040940822526573 := by
  unfold tailWord_4026585
  simp only [CollatzResearch.WordTrace]
  refine ⟨146861620117377705813633209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97907746744918470542422139 146861620117377705813633209)
  ·
    refine ⟨110146215088033279360224907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146861620117377705813633209 110146215088033279360224907)
    ·
      refine ⟨165219322632049919040337361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110146215088033279360224907 165219322632049919040337361)
      ·
        refine ⟨123914491974037439280253021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165219322632049919040337361 123914491974037439280253021)
        ·
          refine ⟨46467934490264039730094883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123914491974037439280253021 46467934490264039730094883)
          ·
            refine ⟨69701901735396059595142325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46467934490264039730094883 69701901735396059595142325)
            ·
              refine ⟨6534553287693380587044593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69701901735396059595142325 6534553287693380587044593)
              ·
                refine ⟨4900914965770035440283445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534553287693380587044593 4900914965770035440283445)
                ·
                  refine ⟨459460778040940822526573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4900914965770035440283445 459460778040940822526573)
                  ·
                    rfl

theorem cell22_4026585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_4026585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026585 prefixEnd_4026585 := by exact prefixLift 4026585
  have htrace : WordTrace (prefixWord ++ tailWord_4026585) baseStart_4026585 baseEnd_4026585 := by
    simpa [prefixWord, tailWord_4026585, baseEnd_4026585] using wordTrace_append hprefix tailTrace_4026585
  have hstable : (prefixWord ++ tailWord_4026585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026585).length < 2 ^ (prefixWord ++ tailWord_4026585).sum := by decide
  have hdescent : baseEnd_4026585 < baseStart_4026585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026589 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_4026589 : Nat := 118140960795 + 4026589 * 2 ^ 59
def prefixEnd_4026589 : Nat := 4983230072969 + 3 ^ 40 * 4026589 * 2
def baseEnd_4026589 : Nat := 1378383703404567790479707

theorem tailTrace_4026589 : CollatzResearch.WordTrace tailWord_4026589 prefixEnd_4026589 1378383703404567790479707 := by
  unfold tailWord_4026589
  simp only [CollatzResearch.WordTrace]
  refine ⟨146861766009363214496778821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97907844006242142997852547 146861766009363214496778821)
  ·
    refine ⟨27536581126755602718146029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146861766009363214496778821 27536581126755602718146029)
    ·
      refine ⟨10326217922533351019304761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27536581126755602718146029 10326217922533351019304761)
      ·
        refine ⟨7744663441900013264478571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10326217922533351019304761 7744663441900013264478571)
        ·
          refine ⟨11616995162850019896717857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744663441900013264478571 11616995162850019896717857)
          ·
            refine ⟨8712746372137514922538393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616995162850019896717857 8712746372137514922538393)
            ·
              refine ⟨6534559779103136191903795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8712746372137514922538393 6534559779103136191903795)
              ·
                refine ⟨9801839668654704287855693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534559779103136191903795 9801839668654704287855693)
                ·
                  refine ⟨3675689875745514107945885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9801839668654704287855693 3675689875745514107945885)
                  ·
                    refine ⟨1378383703404567790479707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675689875745514107945885 1378383703404567790479707)
                    ·
                      rfl

theorem cell22_4026589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_4026589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026589 prefixEnd_4026589 := by exact prefixLift 4026589
  have htrace : WordTrace (prefixWord ++ tailWord_4026589) baseStart_4026589 baseEnd_4026589 := by
    simpa [prefixWord, tailWord_4026589, baseEnd_4026589] using wordTrace_append hprefix tailTrace_4026589
  have hstable : (prefixWord ++ tailWord_4026589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026589).length < 2 ^ (prefixWord ++ tailWord_4026589).sum := by decide
  have hdescent : baseEnd_4026589 < baseStart_4026589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026600 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_4026600 : Nat := 118140960795 + 4026600 * 2 ^ 59
def prefixEnd_4026600 : Nat := 4983230072969 + 3 ^ 40 * 4026600 * 2
def baseEnd_4026600 : Nat := 1378387468929367428454673

theorem tailTrace_4026600 : CollatzResearch.WordTrace tailWord_4026600 prefixEnd_4026600 1378387468929367428454673 := by
  unfold tailWord_4026600
  simp only [CollatzResearch.WordTrace]
  refine ⟨73431083606161681687714627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97908111474882242250286169 73431083606161681687714627)
  ·
    refine ⟨110146625409242522531571941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73431083606161681687714627 110146625409242522531571941)
    ·
      refine ⟨20652492264232972974669739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110146625409242522531571941 20652492264232972974669739)
      ·
        refine ⟨30978738396349459462004609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20652492264232972974669739 30978738396349459462004609)
        ·
          refine ⟨23234053797262094596503457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30978738396349459462004609 23234053797262094596503457)
          ·
            refine ⟨17425540347946570947377593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23234053797262094596503457 17425540347946570947377593)
            ·
              refine ⟨13069155260959928210533195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17425540347946570947377593 13069155260959928210533195)
              ·
                refine ⟨19603732891439892315799793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13069155260959928210533195 19603732891439892315799793)
                ·
                  refine ⟨14702799668579919236849845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19603732891439892315799793 14702799668579919236849845)
                  ·
                    refine ⟨1378387468929367428454673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14702799668579919236849845 1378387468929367428454673)
                    ·
                      rfl

theorem cell22_4026600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_4026600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026600 prefixEnd_4026600 := by exact prefixLift 4026600
  have htrace : WordTrace (prefixWord ++ tailWord_4026600) baseStart_4026600 baseEnd_4026600 := by
    simpa [prefixWord, tailWord_4026600, baseEnd_4026600] using wordTrace_append hprefix tailTrace_4026600
  have hstable : (prefixWord ++ tailWord_4026600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026600).length < 2 ^ (prefixWord ++ tailWord_4026600).sum := by decide
  have hdescent : baseEnd_4026600 < baseStart_4026600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026602 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_4026602 : Nat := 118140960795 + 4026602 * 2 ^ 59
def prefixEnd_4026602 : Nat := 4983230072969 + 3 ^ 40 * 4026602 * 2
def baseEnd_4026602 : Nat := 459462717856746696634889

theorem tailTrace_4026602 : CollatzResearch.WordTrace tailWord_4026602 prefixEnd_4026602 459462717856746696634889 := by
  unfold tailWord_4026602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36715560039579029429250515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97908160105544078478001373 36715560039579029429250515)
  ·
    refine ⟨55073340059368544143875773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36715560039579029429250515 55073340059368544143875773)
    ·
      refine ⟨20652502522263204053953415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55073340059368544143875773 20652502522263204053953415)
      ·
        refine ⟨30978753783394806080930123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20652502522263204053953415 30978753783394806080930123)
        ·
          refine ⟨46468130675092209121395185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30978753783394806080930123 46468130675092209121395185)
          ·
            refine ⟨34851098006319156841046389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46468130675092209121395185 34851098006319156841046389)
            ·
              refine ⟨3267290438092420953848099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34851098006319156841046389 3267290438092420953848099)
              ·
                refine ⟨4900935657138631430772149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267290438092420953848099 4900935657138631430772149)
                ·
                  refine ⟨459462717856746696634889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4900935657138631430772149 459462717856746696634889)
                  ·
                    rfl

theorem cell22_4026602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_4026602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026602 prefixEnd_4026602 := by exact prefixLift 4026602
  have htrace : WordTrace (prefixWord ++ tailWord_4026602) baseStart_4026602 baseEnd_4026602 := by
    simpa [prefixWord, tailWord_4026602, baseEnd_4026602] using wordTrace_append hprefix tailTrace_4026602
  have hstable : (prefixWord ++ tailWord_4026602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026602).length < 2 ^ (prefixWord ++ tailWord_4026602).sum := by decide
  have hdescent : baseEnd_4026602 < baseStart_4026602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026632 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_4026632 : Nat := 118140960795 + 4026632 * 2 ^ 59
def prefixEnd_4026632 : Nat := 4983230072969 + 3 ^ 40 * 4026632 * 2
def baseEnd_4026632 : Nat := 1378398423183330011654575

theorem tailTrace_4026632 : CollatzResearch.WordTrace tailWord_4026632 prefixEnd_4026632 1378398423183330011654575 := by
  unfold tailWord_4026632
  simp only [CollatzResearch.WordTrace]
  refine ⟨73431667174103716420297075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97908889565471621893729433 73431667174103716420297075)
  ·
    refine ⟨110147500761155574630445613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73431667174103716420297075 110147500761155574630445613)
    ·
      refine ⟨41305312785433340486417105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110147500761155574630445613 41305312785433340486417105)
      ·
        refine ⟨30978984589075005364812829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41305312785433340486417105 30978984589075005364812829)
        ·
          refine ⟨11617119220903127011804811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30978984589075005364812829 11617119220903127011804811)
          ·
            refine ⟨17425678831354690517707217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617119220903127011804811 17425678831354690517707217)
            ·
              refine ⟨13069259123516017888280413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17425678831354690517707217 13069259123516017888280413)
              ·
                refine ⟨4900972171318506708105155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13069259123516017888280413 4900972171318506708105155)
                ·
                  refine ⟨7351458256977760062157733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900972171318506708105155 7351458256977760062157733)
                  ·
                    refine ⟨1378398423183330011654575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351458256977760062157733 1378398423183330011654575)
                    ·
                      rfl

theorem cell22_4026632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_4026632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026632 prefixEnd_4026632 := by exact prefixLift 4026632
  have htrace : WordTrace (prefixWord ++ tailWord_4026632) baseStart_4026632 baseEnd_4026632 := by
    simpa [prefixWord, tailWord_4026632, baseEnd_4026632] using wordTrace_append hprefix tailTrace_4026632
  have hstable : (prefixWord ++ tailWord_4026632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026632).length < 2 ^ (prefixWord ++ tailWord_4026632).sum := by decide
  have hdescent : baseEnd_4026632 < baseStart_4026632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026647 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 6]
def baseStart_4026647 : Nat := 118140960795 + 4026647 * 2 ^ 59
def prefixEnd_4026647 : Nat := 4983230072969 + 3 ^ 40 * 4026647 * 2
def baseEnd_4026647 : Nat := 459467852663291657509843

theorem tailTrace_4026647 : CollatzResearch.WordTrace tailWord_4026647 prefixEnd_4026647 459467852663291657509843 := by
  unfold tailWord_4026647
  simp only [CollatzResearch.WordTrace]
  refine ⟨146863881443153090402390195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97909254295435393601593463 146863881443153090402390195)
  ·
    refine ⟨220295822164729635603585293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146863881443153090402390195 220295822164729635603585293)
    ·
      refine ⟨82610933311773613351344485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220295822164729635603585293 82610933311773613351344485)
      ·
        refine ⟨15489549995957552503377091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82610933311773613351344485 15489549995957552503377091)
        ·
          refine ⟨23234324993936328755065637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15489549995957552503377091 23234324993936328755065637)
          ·
            refine ⟨4356435936363061641574807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23234324993936328755065637 4356435936363061641574807)
            ·
              refine ⟨6534653904544592462362211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356435936363061641574807 6534653904544592462362211)
              ·
                refine ⟨9801980856816888693543317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534653904544592462362211 9801980856816888693543317)
                ·
                  refine ⟨459467852663291657509843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9801980856816888693543317 459467852663291657509843)
                  ·
                    rfl

theorem cell22_4026647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 6].length) (baseStart_4026647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026647 prefixEnd_4026647 := by exact prefixLift 4026647
  have htrace : WordTrace (prefixWord ++ tailWord_4026647) baseStart_4026647 baseEnd_4026647 := by
    simpa [prefixWord, tailWord_4026647, baseEnd_4026647] using wordTrace_append hprefix tailTrace_4026647
  have hstable : (prefixWord ++ tailWord_4026647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026647).length < 2 ^ (prefixWord ++ tailWord_4026647).sum := by decide
  have hdescent : baseEnd_4026647 < baseStart_4026647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026666 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4026666 : Nat := 118140960795 + 4026666 * 2 ^ 59
def prefixEnd_4026666 : Nat := 4983230072969 + 3 ^ 40 * 4026666 * 2
def baseEnd_4026666 : Nat := 1378410062078165256304471

theorem tailTrace_4026666 : CollatzResearch.WordTrace tailWord_4026666 prefixEnd_4026666 1378410062078165256304471 := by
  unfold tailWord_4026666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36716143607521064161832963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97909716286722837764887901 36716143607521064161832963)
  ·
    refine ⟨55074215411281596242749445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36716143607521064161832963 55074215411281596242749445)
    ·
      refine ⟨10326415389615299295515521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55074215411281596242749445 10326415389615299295515521)
      ·
        refine ⟨7744811542211474471636641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10326415389615299295515521 7744811542211474471636641)
        ·
          refine ⟨5808608656658605853727481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7744811542211474471636641 5808608656658605853727481)
          ·
            refine ⟨4356456492493954390295611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808608656658605853727481 4356456492493954390295611)
            ·
              refine ⟨6534684738740931585443417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356456492493954390295611 6534684738740931585443417)
              ·
                refine ⟨4901013554055698689082563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534684738740931585443417 4901013554055698689082563)
                ·
                  refine ⟨7351520331083548033623845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901013554055698689082563 7351520331083548033623845)
                  ·
                    refine ⟨1378410062078165256304471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351520331083548033623845 1378410062078165256304471)
                    ·
                      rfl

theorem cell22_4026666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4026666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026666 prefixEnd_4026666 := by exact prefixLift 4026666
  have htrace : WordTrace (prefixWord ++ tailWord_4026666) baseStart_4026666 baseEnd_4026666 := by
    simpa [prefixWord, tailWord_4026666, baseEnd_4026666] using wordTrace_append hprefix tailTrace_4026666
  have hstable : (prefixWord ++ tailWord_4026666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026666).length < 2 ^ (prefixWord ++ tailWord_4026666).sum := by decide
  have hdescent : baseEnd_4026666 < baseStart_4026666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026677 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_4026677 : Nat := 118140960795 + 4026677 * 2 ^ 59
def prefixEnd_4026677 : Nat := 4983230072969 + 3 ^ 40 * 4026677 * 2
def baseEnd_4026677 : Nat := 1378413827602964894279437

theorem tailTrace_4026677 : CollatzResearch.WordTrace tailWord_4026677 prefixEnd_4026677 1378413827602964894279437 := by
  unfold tailWord_4026677
  simp only [CollatzResearch.WordTrace]
  refine ⟨146864975633044405525982285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97909983755362937017321523 146864975633044405525982285)
  ·
    refine ⟨55074365862391652072243357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146864975633044405525982285 55074365862391652072243357)
    ·
      refine ⟨20652887198396869527091259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55074365862391652072243357 20652887198396869527091259)
      ·
        refine ⟨30979330797595304290636889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20652887198396869527091259 30979330797595304290636889)
        ·
          refine ⟨23234498098196478217977667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30979330797595304290636889 23234498098196478217977667)
          ·
            refine ⟨34851747147294717326966501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23234498098196478217977667 34851747147294717326966501)
            ·
              refine ⟨6534702590117759498806219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34851747147294717326966501 6534702590117759498806219)
              ·
                refine ⟨9802053885176639248209329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534702590117759498806219 9802053885176639248209329)
                ·
                  refine ⟨7351540413882479436156997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802053885176639248209329 7351540413882479436156997)
                  ·
                    refine ⟨1378413827602964894279437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351540413882479436156997 1378413827602964894279437)
                    ·
                      rfl

theorem cell22_4026677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_4026677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026677 prefixEnd_4026677 := by exact prefixLift 4026677
  have htrace : WordTrace (prefixWord ++ tailWord_4026677) baseStart_4026677 baseEnd_4026677 := by
    simpa [prefixWord, tailWord_4026677, baseEnd_4026677] using wordTrace_append hprefix tailTrace_4026677
  have hstable : (prefixWord ++ tailWord_4026677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026677).length < 2 ^ (prefixWord ++ tailWord_4026677).sum := by decide
  have hdescent : baseEnd_4026677 < baseStart_4026677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026692 : List Nat := [2, 3, 4, 1, 2, 10]
def baseStart_4026692 : Nat := 118140960795 + 4026692 * 2 ^ 59
def prefixEnd_4026692 : Nat := 4983230072969 + 3 ^ 40 * 4026692 * 2
def baseEnd_4026692 : Nat := 17017518054438393273511

theorem tailTrace_4026692 : CollatzResearch.WordTrace tailWord_4026692 prefixEnd_4026692 17017518054438393273511 := by
  unfold tailWord_4026692
  simp only [CollatzResearch.WordTrace]
  refine ⟨73432761363995031543889165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97910348485326708725185553 73432761363995031543889165)
  ·
    refine ⟨27537285511498136828958437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73432761363995031543889165 27537285511498136828958437)
    ·
      refine ⟨5163241033405900655429707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27537285511498136828958437 5163241033405900655429707)
      ·
        refine ⟨7744861550108850983144561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5163241033405900655429707 7744861550108850983144561)
        ·
          refine ⟨5808646162581638237358421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7744861550108850983144561 5808646162581638237358421)
          ·
            refine ⟨17017518054438393273511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5808646162581638237358421 17017518054438393273511)
            ·
              rfl

theorem cell22_4026692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 10].length) (baseStart_4026692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026692 prefixEnd_4026692 := by exact prefixLift 4026692
  have htrace : WordTrace (prefixWord ++ tailWord_4026692) baseStart_4026692 baseEnd_4026692 := by
    simpa [prefixWord, tailWord_4026692, baseEnd_4026692] using wordTrace_append hprefix tailTrace_4026692
  have hstable : (prefixWord ++ tailWord_4026692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026692).length < 2 ^ (prefixWord ++ tailWord_4026692).sum := by decide
  have hdescent : baseEnd_4026692 < baseStart_4026692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026705 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_4026705 : Nat := 118140960795 + 4026705 * 2 ^ 59
def prefixEnd_4026705 : Nat := 4983230072969 + 3 ^ 40 * 4026705 * 2
def baseEnd_4026705 : Nat := 1378423412575182154579351

theorem tailTrace_4026705 : CollatzResearch.WordTrace tailWord_4026705 prefixEnd_4026705 1378423412575182154579351 := by
  unfold tailWord_4026705
  simp only [CollatzResearch.WordTrace]
  refine ⟨146865996876942966308001569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97910664584628644205334379 146865996876942966308001569)
  ·
    refine ⟨110149497657707224731001177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146865996876942966308001569 110149497657707224731001177)
    ·
      refine ⟨82612123243280418548250883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110149497657707224731001177 82612123243280418548250883)
      ·
        refine ⟨123918184864920627822376325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82612123243280418548250883 123918184864920627822376325)
        ·
          refine ⟨23234659662172617716695561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123918184864920627822376325 23234659662172617716695561)
          ·
            refine ⟨17425994746629463287521671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23234659662172617716695561 17425994746629463287521671)
            ·
              refine ⟨26138992119944194931282507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17425994746629463287521671 26138992119944194931282507)
              ·
                refine ⟨39208488179916292396923761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26138992119944194931282507 39208488179916292396923761)
                ·
                  refine ⟨29406366134937219297692821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39208488179916292396923761 29406366134937219297692821)
                  ·
                    refine ⟨1378423412575182154579351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29406366134937219297692821 1378423412575182154579351)
                    ·
                      rfl

theorem cell22_4026705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_4026705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026705 prefixEnd_4026705 := by exact prefixLift 4026705
  have htrace : WordTrace (prefixWord ++ tailWord_4026705) baseStart_4026705 baseEnd_4026705 := by
    simpa [prefixWord, tailWord_4026705, baseEnd_4026705] using wordTrace_append hprefix tailTrace_4026705
  have hstable : (prefixWord ++ tailWord_4026705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026705).length < 2 ^ (prefixWord ++ tailWord_4026705).sum := by decide
  have hdescent : baseEnd_4026705 < baseStart_4026705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026709 : List Nat := [1, 3, 2, 2, 5, 1, 1, 7]
def baseStart_4026709 : Nat := 118140960795 + 4026709 * 2 ^ 59
def prefixEnd_4026709 : Nat := 4983230072969 + 3 ^ 40 * 4026709 * 2
def baseEnd_4026709 : Nat := 153158309095214164164371

theorem tailTrace_4026709 : CollatzResearch.WordTrace tailWord_4026709 prefixEnd_4026709 153158309095214164164371 := by
  unfold tailWord_4026709
  simp only [CollatzResearch.WordTrace]
  refine ⟨146866142768928474991147181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97910761845952316660764787 146866142768928474991147181)
  ·
    refine ⟨55074803538348178121680193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146866142768928474991147181 55074803538348178121680193)
    ·
      refine ⟨41306102653761133591260145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55074803538348178121680193 41306102653761133591260145)
      ·
        refine ⟨30979576990320850193445109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41306102653761133591260145 30979576990320850193445109)
        ·
          refine ⟨2904335342842579705635479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30979576990320850193445109 2904335342842579705635479)
          ·
            refine ⟨4356503014263869558453219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904335342842579705635479 4356503014263869558453219)
            ·
              refine ⟨6534754521395804337679829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356503014263869558453219 6534754521395804337679829)
              ·
                refine ⟨153158309095214164164371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6534754521395804337679829 153158309095214164164371)
                ·
                  rfl

theorem cell22_4026709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 7].length) (baseStart_4026709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026709 prefixEnd_4026709 := by exact prefixLift 4026709
  have htrace : WordTrace (prefixWord ++ tailWord_4026709) baseStart_4026709 baseEnd_4026709 := by
    simpa [prefixWord, tailWord_4026709, baseEnd_4026709] using wordTrace_append hprefix tailTrace_4026709
  have hstable : (prefixWord ++ tailWord_4026709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026709).length < 2 ^ (prefixWord ++ tailWord_4026709).sum := by decide
  have hdescent : baseEnd_4026709 < baseStart_4026709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026741 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_4026741 : Nat := 118140960795 + 4026741 * 2 ^ 59
def prefixEnd_4026741 : Nat := 4983230072969 + 3 ^ 40 * 4026741 * 2
def baseEnd_4026741 : Nat := 1378435736110890060679241

theorem tailTrace_4026741 : CollatzResearch.WordTrace tailWord_4026741 prefixEnd_4026741 1378435736110890060679241 := by
  unfold tailWord_4026741
  simp only [CollatzResearch.WordTrace]
  refine ⟨146867309904812544456312077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97911539936541696304208051 146867309904812544456312077)
  ·
    refine ⟨55075241214304704171117029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146867309904812544456312077 55075241214304704171117029)
    ·
      refine ⟨10326607727682132032084443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55075241214304704171117029 10326607727682132032084443)
      ·
        refine ⟨15489911591523198048126665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326607727682132032084443 15489911591523198048126665)
        ·
          refine ⟨11617433693642398536094999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15489911591523198048126665 11617433693642398536094999)
          ·
            refine ⟨17426150540463597804142499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617433693642398536094999 17426150540463597804142499)
            ·
              refine ⟨26139225810695396706213749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426150540463597804142499 26139225810695396706213749)
              ·
                refine ⟨2450552419752693441207539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26139225810695396706213749 2450552419752693441207539)
                ·
                  refine ⟨3675828629629040161811309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450552419752693441207539 3675828629629040161811309)
                  ·
                    refine ⟨1378435736110890060679241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675828629629040161811309 1378435736110890060679241)
                    ·
                      rfl

theorem cell22_4026741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_4026741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026741 prefixEnd_4026741 := by exact prefixLift 4026741
  have htrace : WordTrace (prefixWord ++ tailWord_4026741) baseStart_4026741 baseEnd_4026741 := by
    simpa [prefixWord, tailWord_4026741, baseEnd_4026741] using wordTrace_append hprefix tailTrace_4026741
  have hstable : (prefixWord ++ tailWord_4026741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026741).length < 2 ^ (prefixWord ++ tailWord_4026741).sum := by decide
  have hdescent : baseEnd_4026741 < baseStart_4026741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026784 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_4026784 : Nat := 118140960795 + 4026784 * 2 ^ 59
def prefixEnd_4026784 : Nat := 4983230072969 + 3 ^ 40 * 4026784 * 2
def baseEnd_4026784 : Nat := 1378450455889652281854109

theorem tailTrace_4026784 : CollatzResearch.WordTrace tailWord_4026784 prefixEnd_4026784 1378450455889652281854109 := by
  unfold tailWord_4026784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73434439121828381400063703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97912585495771175200084937 73434439121828381400063703)
  ·
    refine ⟨110151658682742572100095555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73434439121828381400063703 110151658682742572100095555)
    ·
      refine ⟨165227488024113858150143333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110151658682742572100095555 165227488024113858150143333)
      ·
        refine ⟨30980154004521348403151875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165227488024113858150143333 30980154004521348403151875)
        ·
          refine ⟨46470231006782022604727813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30980154004521348403151875 46470231006782022604727813)
          ·
            refine ⟨8713168313771629238386465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46470231006782022604727813 8713168313771629238386465)
            ·
              refine ⟨6534876235328721928789849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8713168313771629238386465 6534876235328721928789849)
              ·
                refine ⟨4901157176496541446592387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534876235328721928789849 4901157176496541446592387)
                ·
                  refine ⟨7351735764744812169888581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901157176496541446592387 7351735764744812169888581)
                  ·
                    refine ⟨1378450455889652281854109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351735764744812169888581 1378450455889652281854109)
                    ·
                      rfl

theorem cell22_4026784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_4026784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026784 prefixEnd_4026784 := by exact prefixLift 4026784
  have htrace : WordTrace (prefixWord ++ tailWord_4026784) baseStart_4026784 baseEnd_4026784 := by
    simpa [prefixWord, tailWord_4026784, baseEnd_4026784] using wordTrace_append hprefix tailTrace_4026784
  have hstable : (prefixWord ++ tailWord_4026784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026784).length < 2 ^ (prefixWord ++ tailWord_4026784).sum := by decide
  have hdescent : baseEnd_4026784 < baseStart_4026784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026814 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_4026814 : Nat := 118140960795 + 4026814 * 2 ^ 59
def prefixEnd_4026814 : Nat := 4983230072969 + 3 ^ 40 * 4026814 * 2
def baseEnd_4026814 : Nat := 1378460725502742203604017

theorem tailTrace_4026814 : CollatzResearch.WordTrace tailWord_4026814 prefixEnd_4026814 1378460725502742203604017 := by
  unfold tailWord_4026814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18358746554193509740464937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97913314955698718615812997 18358746554193509740464937)
  ·
    refine ⟨13769059915645132305348703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18358746554193509740464937 13769059915645132305348703)
    ·
      refine ⟨20653589873467698458023055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13769059915645132305348703 20653589873467698458023055)
      ·
        refine ⟨30980384810201547687034583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20653589873467698458023055 30980384810201547687034583)
        ·
          refine ⟨46470577215302321530551875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30980384810201547687034583 46470577215302321530551875)
          ·
            refine ⟨69705865822953482295827813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46470577215302321530551875 69705865822953482295827813)
            ·
              refine ⟨13069849841803777930467715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69705865822953482295827813 13069849841803777930467715)
              ·
                refine ⟨19604774762705666895701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13069849841803777930467715 19604774762705666895701573)
                ·
                  refine ⟨3675895268007312542944045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19604774762705666895701573 3675895268007312542944045)
                  ·
                    refine ⟨1378460725502742203604017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675895268007312542944045 1378460725502742203604017)
                    ·
                      rfl

theorem cell22_4026814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_4026814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026814 prefixEnd_4026814 := by exact prefixLift 4026814
  have htrace : WordTrace (prefixWord ++ tailWord_4026814) baseStart_4026814 baseEnd_4026814 := by
    simpa [prefixWord, tailWord_4026814, baseEnd_4026814] using wordTrace_append hprefix tailTrace_4026814
  have hstable : (prefixWord ++ tailWord_4026814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026814).length < 2 ^ (prefixWord ++ tailWord_4026814).sum := by decide
  have hdescent : baseEnd_4026814 < baseStart_4026814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026893 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4026893 : Nat := 118140960795 + 4026893 * 2 ^ 59
def prefixEnd_4026893 : Nat := 4983230072969 + 3 ^ 40 * 4026893 * 2
def baseEnd_4026893 : Nat := 1378487768817212330878775

theorem tailTrace_4026893 : CollatzResearch.WordTrace tailWord_4026893 prefixEnd_4026893 1378487768817212330878775 := by
  unfold tailWord_4026893
  simp only [CollatzResearch.WordTrace]
  refine ⟨146872853800261874415845333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97915235866841249610563555 146872853800261874415845333)
  ·
    refine ⟨3442332510943637681621375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 146872853800261874415845333 3442332510943637681621375)
    ·
      refine ⟨5163498766415456522432063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442332510943637681621375 5163498766415456522432063)
      ·
        refine ⟨7745248149623184783648095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5163498766415456522432063 7745248149623184783648095)
        ·
          refine ⟨11617872224434777175472143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7745248149623184783648095 11617872224434777175472143)
          ·
            refine ⟨17426808336652165763208215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617872224434777175472143 17426808336652165763208215)
            ·
              refine ⟨26140212504978248644812323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426808336652165763208215 26140212504978248644812323)
              ·
                refine ⟨39210318757467372967218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26140212504978248644812323 39210318757467372967218485)
                ·
                  refine ⟨3675967383512566215676733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39210318757467372967218485 3675967383512566215676733)
                  ·
                    refine ⟨1378487768817212330878775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675967383512566215676733 1378487768817212330878775)
                    ·
                      rfl

theorem cell22_4026893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4026893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026893 prefixEnd_4026893 := by exact prefixLift 4026893
  have htrace : WordTrace (prefixWord ++ tailWord_4026893) baseStart_4026893 baseEnd_4026893 := by
    simpa [prefixWord, tailWord_4026893, baseEnd_4026893] using wordTrace_append hprefix tailTrace_4026893
  have hstable : (prefixWord ++ tailWord_4026893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026893).length < 2 ^ (prefixWord ++ tailWord_4026893).sum := by decide
  have hdescent : baseEnd_4026893 < baseStart_4026893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026949 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_4026949 : Nat := 118140960795 + 4026949 * 2 ^ 59
def prefixEnd_4026949 : Nat := 4983230072969 + 3 ^ 40 * 4026949 * 2
def baseEnd_4026949 : Nat := 1378506938761646851478603

theorem tailTrace_4026949 : CollatzResearch.WordTrace tailWord_4026949 prefixEnd_4026949 1378506938761646851478603 := by
  unfold tailWord_4026949
  simp only [CollatzResearch.WordTrace]
  refine ⟨146874896288058995979883901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97916597525372663986589267 146874896288058995979883901)
  ·
    refine ⟨55078086108022123492456463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146874896288058995979883901 55078086108022123492456463)
    ·
      refine ⟨82617129162033185238684695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55078086108022123492456463 82617129162033185238684695)
      ·
        refine ⟨123925693743049777858027043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82617129162033185238684695 123925693743049777858027043)
        ·
          refine ⟨185888540614574666787040565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123925693743049777858027043 185888540614574666787040565)
          ·
            refine ⟨17427050682616375011285053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185888540614574666787040565 17427050682616375011285053)
            ·
              refine ⟨6535144005981140629231895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17427050682616375011285053 6535144005981140629231895)
              ·
                refine ⟨9802716008971710943847843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535144005981140629231895 9802716008971710943847843)
                ·
                  refine ⟨14704074013457566415771765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802716008971710943847843 14704074013457566415771765)
                  ·
                    refine ⟨1378506938761646851478603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14704074013457566415771765 1378506938761646851478603)
                    ·
                      rfl

theorem cell22_4026949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_4026949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026949 prefixEnd_4026949 := by exact prefixLift 4026949
  have htrace : WordTrace (prefixWord ++ tailWord_4026949) baseStart_4026949 baseEnd_4026949 := by
    simpa [prefixWord, tailWord_4026949, baseEnd_4026949] using wordTrace_append hprefix tailTrace_4026949
  have hstable : (prefixWord ++ tailWord_4026949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026949).length < 2 ^ (prefixWord ++ tailWord_4026949).sum := by decide
  have hdescent : baseEnd_4026949 < baseStart_4026949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026964 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4026964 : Nat := 118140960795 + 4026964 * 2 ^ 59
def prefixEnd_4026964 : Nat := 4983230072969 + 3 ^ 40 * 4026964 * 2
def baseEnd_4026964 : Nat := 1378512073568191812353557

theorem tailTrace_4026964 : CollatzResearch.WordTrace tailWord_4026964 prefixEnd_4026964 1378512073568191812353557 := by
  unfold tailWord_4026964
  simp only [CollatzResearch.WordTrace]
  refine ⟨73437721691502326770839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97916962255336435694453297 73437721691502326770839973)
  ·
    refine ⟨13769572817156686269532495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73437721691502326770839973 13769572817156686269532495)
    ·
      refine ⟨20654359225735029404298743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13769572817156686269532495 20654359225735029404298743)
      ·
        refine ⟨30981538838602544106448115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20654359225735029404298743 30981538838602544106448115)
        ·
          refine ⟨46472308257903816159672173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30981538838602544106448115 46472308257903816159672173)
          ·
            refine ⟨17427115596713931059877065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46472308257903816159672173 17427115596713931059877065)
            ·
              refine ⟨13070336697535448294907799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17427115596713931059877065 13070336697535448294907799)
              ·
                refine ⟨19605505046303172442361699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13070336697535448294907799 19605505046303172442361699)
                ·
                  refine ⟨29408257569454758663542549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19605505046303172442361699 29408257569454758663542549)
                  ·
                    refine ⟨1378512073568191812353557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29408257569454758663542549 1378512073568191812353557)
                    ·
                      rfl

theorem cell22_4026964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4026964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026964 prefixEnd_4026964 := by exact prefixLift 4026964
  have htrace : WordTrace (prefixWord ++ tailWord_4026964) baseStart_4026964 baseEnd_4026964 := by
    simpa [prefixWord, tailWord_4026964, baseEnd_4026964] using wordTrace_append hprefix tailTrace_4026964
  have hstable : (prefixWord ++ tailWord_4026964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026964).length < 2 ^ (prefixWord ++ tailWord_4026964).sum := by decide
  have hdescent : baseEnd_4026964 < baseStart_4026964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4026981 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_4026981 : Nat := 118140960795 + 4026981 * 2 ^ 59
def prefixEnd_4026981 : Nat := 4983230072969 + 3 ^ 40 * 4026981 * 2
def baseEnd_4026981 : Nat := 1378517893015609434678505

theorem tailTrace_4026981 : CollatzResearch.WordTrace tailWord_4026981 prefixEnd_4026981 1378517893015609434678505 := by
  unfold tailWord_4026981
  simp only [CollatzResearch.WordTrace]
  refine ⟨146876063423943065445048797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97917375615962043630032531 146876063423943065445048797)
  ·
    refine ⟨55078523783978649541893299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146876063423943065445048797 55078523783978649541893299)
    ·
      refine ⟨82617785675967974312839949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55078523783978649541893299 82617785675967974312839949)
      ·
        refine ⟨30981669628487990367314981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82617785675967974312839949 30981669628487990367314981)
        ·
          refine ⟨5809063055341498193871559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30981669628487990367314981 5809063055341498193871559)
          ·
            refine ⟨8713594583012247290807339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809063055341498193871559 8713594583012247290807339)
            ·
              refine ⟨13070391874518370936211009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713594583012247290807339 13070391874518370936211009)
              ·
                refine ⟨9802793905888778202158257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070391874518370936211009 9802793905888778202158257)
                ·
                  refine ⟨7352095429416583651618693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802793905888778202158257 7352095429416583651618693)
                  ·
                    refine ⟨1378517893015609434678505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352095429416583651618693 1378517893015609434678505)
                    ·
                      rfl

theorem cell22_4026981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_4026981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4026981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4026981 prefixEnd_4026981 := by exact prefixLift 4026981
  have htrace : WordTrace (prefixWord ++ tailWord_4026981) baseStart_4026981 baseEnd_4026981 := by
    simpa [prefixWord, tailWord_4026981, baseEnd_4026981] using wordTrace_append hprefix tailTrace_4026981
  have hstable : (prefixWord ++ tailWord_4026981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4026981).length < 2 ^ (prefixWord ++ tailWord_4026981).sum := by decide
  have hdescent : baseEnd_4026981 < baseStart_4026981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4026981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027007 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 9]
def baseStart_4027007 : Nat := 118140960795 + 4027007 * 2 ^ 59
def prefixEnd_4027007 : Nat := 4983230072969 + 3 ^ 40 * 4027007 * 2
def baseEnd_4027007 : Nat := 459508931115651344509475

theorem tailTrace_4027007 : CollatzResearch.WordTrace tailWord_4027007 prefixEnd_4027007 459508931115651344509475 := by
  unfold tailWord_4027007
  simp only [CollatzResearch.WordTrace]
  refine ⟨146877011721848871885495275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97918007814565914590330183 146877011721848871885495275)
  ·
    refine ⟨220315517582773307828242913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146877011721848871885495275 220315517582773307828242913)
    ·
      refine ⟨165236638187079980871182185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220315517582773307828242913 165236638187079980871182185)
      ·
        refine ⟨123927478640309985653386639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165236638187079980871182185 123927478640309985653386639)
        ·
          refine ⟨185891217960464978480079959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123927478640309985653386639 185891217960464978480079959)
          ·
            refine ⟨278836826940697467720119939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185891217960464978480079959 278836826940697467720119939)
            ·
              refine ⟨418255240411046201580179909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278836826940697467720119939 418255240411046201580179909)
              ·
                refine ⟨78422857577071162796283733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418255240411046201580179909 78422857577071162796283733)
                ·
                  refine ⟨459508931115651344509475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78422857577071162796283733 459508931115651344509475)
                  ·
                    rfl

theorem cell22_4027007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_4027007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027007 prefixEnd_4027007 := by exact prefixLift 4027007
  have htrace : WordTrace (prefixWord ++ tailWord_4027007) baseStart_4027007 baseEnd_4027007 := by
    simpa [prefixWord, tailWord_4027007, baseEnd_4027007] using wordTrace_append hprefix tailTrace_4027007
  have hstable : (prefixWord ++ tailWord_4027007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027007).length < 2 ^ (prefixWord ++ tailWord_4027007).sum := by decide
  have hdescent : baseEnd_4027007 < baseStart_4027007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027069 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 8]
def baseStart_4027069 : Nat := 118140960795 + 4027069 * 2 ^ 59
def prefixEnd_4027069 : Nat := 4983230072969 + 3 ^ 40 * 4027069 * 2
def baseEnd_4027069 : Nat := 459516005738002179492745

theorem tailTrace_4027069 : CollatzResearch.WordTrace tailWord_4027069 prefixEnd_4027069 459516005738002179492745 := by
  unfold tailWord_4027069
  simp only [CollatzResearch.WordTrace]
  refine ⟨146879273047624256474252261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97919515365082837649501507 146879273047624256474252261)
  ·
    refine ⟨27539863696429548088922299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146879273047624256474252261 27539863696429548088922299)
    ·
      refine ⟨41309795544644322133383449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27539863696429548088922299 41309795544644322133383449)
      ·
        refine ⟨30982346658483241600037587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41309795544644322133383449 30982346658483241600037587)
        ·
          refine ⟨46473519987724862400056381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982346658483241600037587 46473519987724862400056381)
          ·
            refine ⟨17427569995396823400021143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46473519987724862400056381 17427569995396823400021143)
            ·
              refine ⟨26141354993095235100031715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17427569995396823400021143 26141354993095235100031715)
              ·
                refine ⟨39212032489642852650047573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26141354993095235100031715 39212032489642852650047573)
                ·
                  refine ⟨459516005738002179492745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39212032489642852650047573 459516005738002179492745)
                  ·
                    rfl

theorem cell22_4027069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_4027069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027069 prefixEnd_4027069 := by exact prefixLift 4027069
  have htrace : WordTrace (prefixWord ++ tailWord_4027069) baseStart_4027069 baseEnd_4027069 := by
    simpa [prefixWord, tailWord_4027069, baseEnd_4027069] using wordTrace_append hprefix tailTrace_4027069
  have hstable : (prefixWord ++ tailWord_4027069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027069).length < 2 ^ (prefixWord ++ tailWord_4027069).sum := by decide
  have hdescent : baseEnd_4027069 < baseStart_4027069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027114 : List Nat := [3, 1, 3, 1, 1, 1, 1, 11]
def baseStart_4027114 : Nat := 118140960795 + 4027114 * 2 ^ 59
def prefixEnd_4027114 : Nat := 4983230072969 + 3 ^ 40 * 4027114 * 2
def baseEnd_4027114 : Nat := 153173713514849046789233

theorem tailTrace_4027114 : CollatzResearch.WordTrace tailWord_4027114 prefixEnd_4027114 153173713514849046789233 := by
  unfold tailWord_4027114
  simp only [CollatzResearch.WordTrace]
  refine ⟨36720228583115307289910099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97920609554974152773093597 36720228583115307289910099)
  ·
    refine ⟨55080342874672960934865149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36720228583115307289910099 55080342874672960934865149)
    ·
      refine ⟨20655128578002360350574431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55080342874672960934865149 20655128578002360350574431)
      ·
        refine ⟨30982692867003540525861647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655128578002360350574431 30982692867003540525861647)
        ·
          refine ⟨46474039300505310788792471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982692867003540525861647 46474039300505310788792471)
          ·
            refine ⟨69711058950757966183188707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46474039300505310788792471 69711058950757966183188707)
            ·
              refine ⟨104566588426136949274783061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69711058950757966183188707 104566588426136949274783061)
              ·
                refine ⟨153173713514849046789233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 104566588426136949274783061 153173713514849046789233)
                ·
                  rfl

theorem cell22_4027114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_4027114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027114 prefixEnd_4027114 := by exact prefixLift 4027114
  have htrace : WordTrace (prefixWord ++ tailWord_4027114) baseStart_4027114 baseEnd_4027114 := by
    simpa [prefixWord, tailWord_4027114, baseEnd_4027114] using wordTrace_append hprefix tailTrace_4027114
  have hstable : (prefixWord ++ tailWord_4027114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027114).length < 2 ^ (prefixWord ++ tailWord_4027114).sum := by decide
  have hdescent : baseEnd_4027114 < baseStart_4027114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027118 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_4027118 : Nat := 118140960795 + 4027118 * 2 ^ 59
def prefixEnd_4027118 : Nat := 4983230072969 + 3 ^ 40 * 4027118 * 2
def baseEnd_4027118 : Nat := 1378564790915386744003085

theorem tailTrace_4027118 : CollatzResearch.WordTrace tailWord_4027118 prefixEnd_4027118 1378564790915386744003085 := by
  unfold tailWord_4027118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18360132528055842230348251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97920706816297825228524005 18360132528055842230348251)
  ·
    refine ⟨27540198792083763345522377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18360132528055842230348251 27540198792083763345522377)
    ·
      refine ⟨20655149094062822509141783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27540198792083763345522377 20655149094062822509141783)
      ·
        refine ⟨30982723641094233763712675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655149094062822509141783 30982723641094233763712675)
        ·
          refine ⟨46474085461641350645569013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982723641094233763712675 46474085461641350645569013)
          ·
            refine ⟨4356945512028876623022095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46474085461641350645569013 4356945512028876623022095)
            ·
              refine ⟨6535418268043314934533143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356945512028876623022095 6535418268043314934533143)
              ·
                refine ⟨9803127402064972401799715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535418268043314934533143 9803127402064972401799715)
                ·
                  refine ⟨14704691103097458602699573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803127402064972401799715 14704691103097458602699573)
                  ·
                    refine ⟨1378564790915386744003085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14704691103097458602699573 1378564790915386744003085)
                    ·
                      rfl

theorem cell22_4027118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_4027118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027118 prefixEnd_4027118 := by exact prefixLift 4027118
  have htrace : WordTrace (prefixWord ++ tailWord_4027118) baseStart_4027118 baseEnd_4027118 := by
    simpa [prefixWord, tailWord_4027118, baseEnd_4027118] using wordTrace_append hprefix tailTrace_4027118
  have hstable : (prefixWord ++ tailWord_4027118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027118).length < 2 ^ (prefixWord ++ tailWord_4027118).sum := by decide
  have hdescent : baseEnd_4027118 < baseStart_4027118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027221 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 6]
def baseStart_4027221 : Nat := 118140960795 + 4027221 * 2 ^ 59
def prefixEnd_4027221 : Nat := 4983230072969 + 3 ^ 40 * 4027221 * 2
def baseEnd_4027221 : Nat := 459533349973442936225923

theorem tailTrace_4027221 : CollatzResearch.WordTrace tailWord_4027221 prefixEnd_4027221 459533349973442936225923 := by
  unfold tailWord_4027221
  simp only [CollatzResearch.WordTrace]
  refine ⟨146884816943073586433785517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97923211295382390955857011 146884816943073586433785517)
  ·
    refine ⟨55081806353652594912669569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146884816943073586433785517 55081806353652594912669569)
    ·
      refine ⟨41311354765239446184502177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55081806353652594912669569 41311354765239446184502177)
      ·
        refine ⟨30983516073929584638376633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41311354765239446184502177 30983516073929584638376633)
        ·
          refine ⟨23237637055447188478782475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30983516073929584638376633 23237637055447188478782475)
          ·
            refine ⟨34856455583170782718173713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23237637055447188478782475 34856455583170782718173713)
            ·
              refine ⟨26142341687378087038630285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34856455583170782718173713 26142341687378087038630285)
              ·
                refine ⟨9803378132766782639486357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26142341687378087038630285 9803378132766782639486357)
                ·
                  refine ⟨459533349973442936225923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9803378132766782639486357 459533349973442936225923)
                  ·
                    rfl

theorem cell22_4027221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_4027221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027221 prefixEnd_4027221 := by exact prefixLift 4027221
  have htrace : WordTrace (prefixWord ++ tailWord_4027221) baseStart_4027221 baseEnd_4027221 := by
    simpa [prefixWord, tailWord_4027221, baseEnd_4027221] using wordTrace_append hprefix tailTrace_4027221
  have hstable : (prefixWord ++ tailWord_4027221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027221).length < 2 ^ (prefixWord ++ tailWord_4027221).sum := by decide
  have hdescent : baseEnd_4027221 < baseStart_4027221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027253 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4027253 : Nat := 118140960795 + 4027253 * 2 ^ 59
def prefixEnd_4027253 : Nat := 4983230072969 + 3 ^ 40 * 4027253 * 2
def baseEnd_4027253 : Nat := 1378611004174291391877671

theorem tailTrace_4027253 : CollatzResearch.WordTrace tailWord_4027253 prefixEnd_4027253 1378611004174291391877671 := by
  unfold tailWord_4027253
  simp only [CollatzResearch.WordTrace]
  refine ⟨146885984078957655898950413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97923989385971770599300275 146885984078957655898950413)
  ·
    refine ⟨55082244029609120962106405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146885984078957655898950413 55082244029609120962106405)
    ·
      refine ⟨10327920755551710180394951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55082244029609120962106405 10327920755551710180394951)
      ·
        refine ⟨15491881133327565270592427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327920755551710180394951 15491881133327565270592427)
        ·
          refine ⟨23237821699991347905888641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15491881133327565270592427 23237821699991347905888641)
          ·
            refine ⟨17428366274993510929416481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23237821699991347905888641 17428366274993510929416481)
            ·
              refine ⟨13071274706245133197062361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17428366274993510929416481 13071274706245133197062361)
              ·
                refine ⟨9803456029683849897796771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13071274706245133197062361 9803456029683849897796771)
                ·
                  refine ⟨14705184044525774846695157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803456029683849897796771 14705184044525774846695157)
                  ·
                    refine ⟨1378611004174291391877671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14705184044525774846695157 1378611004174291391877671)
                    ·
                      rfl

theorem cell22_4027253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4027253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027253 prefixEnd_4027253 := by exact prefixLift 4027253
  have htrace : WordTrace (prefixWord ++ tailWord_4027253) baseStart_4027253 baseEnd_4027253 := by
    simpa [prefixWord, tailWord_4027253, baseEnd_4027253] using wordTrace_append hprefix tailTrace_4027253
  have hstable : (prefixWord ++ tailWord_4027253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027253).length < 2 ^ (prefixWord ++ tailWord_4027253).sum := by decide
  have hdescent : baseEnd_4027253 < baseStart_4027253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027296 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_4027296 : Nat := 118140960795 + 4027296 * 2 ^ 59
def prefixEnd_4027296 : Nat := 4983230072969 + 3 ^ 40 * 4027296 * 2
def baseEnd_4027296 : Nat := 1378625723953053613052539

theorem tailTrace_4027296 : CollatzResearch.WordTrace tailWord_4027296 prefixEnd_4027296 1378625723953053613052539 := by
  unfold tailWord_4027296
  simp only [CollatzResearch.WordTrace]
  refine ⟨73443776208900937121382871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97925034945201249495177161 73443776208900937121382871)
  ·
    refine ⟨110165664313351405682074307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73443776208900937121382871 110165664313351405682074307)
    ·
      refine ⟨165248496470027108523111461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110165664313351405682074307 165248496470027108523111461)
      ·
        refine ⟨30984093088130082848083399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165248496470027108523111461 30984093088130082848083399)
        ·
          refine ⟨46476139632195124272125099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30984093088130082848083399 46476139632195124272125099)
          ·
            refine ⟨69714209448292686408187649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46476139632195124272125099 69714209448292686408187649)
            ·
              refine ⟨52285657086219514806140737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69714209448292686408187649 52285657086219514806140737)
              ·
                refine ⟨39214242814664636104605553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52285657086219514806140737 39214242814664636104605553)
                ·
                  refine ⟨29410682110998477078454165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39214242814664636104605553 29410682110998477078454165)
                  ·
                    refine ⟨1378625723953053613052539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29410682110998477078454165 1378625723953053613052539)
                    ·
                      rfl

theorem cell22_4027296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_4027296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027296 prefixEnd_4027296 := by exact prefixLift 4027296
  have htrace : WordTrace (prefixWord ++ tailWord_4027296) baseStart_4027296 baseEnd_4027296 := by
    simpa [prefixWord, tailWord_4027296, baseEnd_4027296] using wordTrace_append hprefix tailTrace_4027296
  have hstable : (prefixWord ++ tailWord_4027296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027296).length < 2 ^ (prefixWord ++ tailWord_4027296).sum := by decide
  have hdescent : baseEnd_4027296 < baseStart_4027296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027315 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 1, 3]
def baseStart_4027315 : Nat := 118140960795 + 4027315 * 2 ^ 59
def prefixEnd_4027315 : Nat := 4983230072969 + 3 ^ 40 * 4027315 * 2
def baseEnd_4027315 : Nat := 1378632228041343896827481

theorem tailTrace_4027315 : CollatzResearch.WordTrace tailWord_4027315 prefixEnd_4027315 1378632228041343896827481 := by
  unfold tailWord_4027315
  simp only [CollatzResearch.WordTrace]
  refine ⟨146888245404733040487707399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97925496936488693658471599 146888245404733040487707399)
  ·
    refine ⟨220332368107099560731561099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146888245404733040487707399 220332368107099560731561099)
    ·
      refine ⟨330498552160649341097341649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220332368107099560731561099 330498552160649341097341649)
      ·
        refine ⟨247873914120487005823006237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330498552160649341097341649 247873914120487005823006237)
        ·
          refine ⟨92952717795182627183627339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247873914120487005823006237 92952717795182627183627339)
          ·
            refine ⟨139429076692773940775441009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92952717795182627183627339 139429076692773940775441009)
            ·
              refine ⟨104571807519580455581580757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139429076692773940775441009 104571807519580455581580757)
              ·
                refine ⟨2450901738740166927693299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104571807519580455581580757 2450901738740166927693299)
                ·
                  refine ⟨3676352608110250391539949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450901738740166927693299 3676352608110250391539949)
                  ·
                    refine ⟨1378632228041343896827481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676352608110250391539949 1378632228041343896827481)
                    ·
                      rfl

theorem cell22_4027315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 3].length) (baseStart_4027315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027315 prefixEnd_4027315 := by exact prefixLift 4027315
  have htrace : WordTrace (prefixWord ++ tailWord_4027315) baseStart_4027315 baseEnd_4027315 := by
    simpa [prefixWord, tailWord_4027315, baseEnd_4027315] using wordTrace_append hprefix tailTrace_4027315
  have hstable : (prefixWord ++ tailWord_4027315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027315).length < 2 ^ (prefixWord ++ tailWord_4027315).sum := by decide
  have hdescent : baseEnd_4027315 < baseStart_4027315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027420 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_4027420 : Nat := 118140960795 + 4027420 * 2 ^ 59
def prefixEnd_4027420 : Nat := 4983230072969 + 3 ^ 40 * 4027420 * 2
def baseEnd_4027420 : Nat := 1378668171687158622952159

theorem tailTrace_4027420 : CollatzResearch.WordTrace tailWord_4027420 prefixEnd_4027420 1378668171687158622952159 := by
  unfold tailWord_4027420
  simp only [CollatzResearch.WordTrace]
  refine ⟨73446037534676321710139857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97928050046235095613519809 73446037534676321710139857)
  ·
    refine ⟨55084528151007241282604893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73446037534676321710139857 55084528151007241282604893)
    ·
      refine ⟨20656698056627715480976835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55084528151007241282604893 20656698056627715480976835)
      ·
        refine ⟨30985047084941573221465253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20656698056627715480976835 30985047084941573221465253)
        ·
          refine ⟨5809696328426544979024735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30985047084941573221465253 5809696328426544979024735)
          ·
            refine ⟨8714544492639817468537103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809696328426544979024735 8714544492639817468537103)
            ·
              refine ⟨13071816738959726202805655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714544492639817468537103 13071816738959726202805655)
              ·
                refine ⟨19607725108439589304208483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13071816738959726202805655 19607725108439589304208483)
                ·
                  refine ⟨29411587662659383956312725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19607725108439589304208483 29411587662659383956312725)
                  ·
                    refine ⟨1378668171687158622952159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29411587662659383956312725 1378668171687158622952159)
                    ·
                      rfl

theorem cell22_4027420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_4027420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027420 prefixEnd_4027420 := by exact prefixLift 4027420
  have htrace : WordTrace (prefixWord ++ tailWord_4027420) baseStart_4027420 baseEnd_4027420 := by
    simpa [prefixWord, tailWord_4027420, baseEnd_4027420] using wordTrace_append hprefix tailTrace_4027420
  have hstable : (prefixWord ++ tailWord_4027420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027420).length < 2 ^ (prefixWord ++ tailWord_4027420).sum := by decide
  have hdescent : baseEnd_4027420 < baseStart_4027420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027424 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 4]
def baseStart_4027424 : Nat := 118140960795 + 4027424 * 2 ^ 59
def prefixEnd_4027424 : Nat := 4983230072969 + 3 ^ 40 * 4027424 * 2
def baseEnd_4027424 : Nat := 459556513656301315284049

theorem tailTrace_4027424 : CollatzResearch.WordTrace tailWord_4027424 prefixEnd_4027424 459556513656301315284049 := by
  unfold tailWord_4027424
  simp only [CollatzResearch.WordTrace]
  refine ⟨73446110480669076051712663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97928147307558768068950217 73446110480669076051712663)
  ·
    refine ⟨110169165721003614077568995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73446110480669076051712663 110169165721003614077568995)
    ·
      refine ⟨165253748581505421116353493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110169165721003614077568995 165253748581505421116353493)
      ·
        refine ⟨3873134732379033307414535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 165253748581505421116353493 3873134732379033307414535)
        ·
          refine ⟨5809702098568549961121803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873134732379033307414535 5809702098568549961121803)
          ·
            refine ⟨8714553147852824941682705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809702098568549961121803 8714553147852824941682705)
            ·
              refine ⟨6535914860889618706262029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8714553147852824941682705 6535914860889618706262029)
              ·
                refine ⟨2450968072833607014848261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6535914860889618706262029 2450968072833607014848261)
                ·
                  refine ⟨459556513656301315284049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2450968072833607014848261 459556513656301315284049)
                  ·
                    rfl

theorem cell22_4027424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_4027424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027424 prefixEnd_4027424 := by exact prefixLift 4027424
  have htrace : WordTrace (prefixWord ++ tailWord_4027424) baseStart_4027424 baseEnd_4027424 := by
    simpa [prefixWord, tailWord_4027424, baseEnd_4027424] using wordTrace_append hprefix tailTrace_4027424
  have hstable : (prefixWord ++ tailWord_4027424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027424).length < 2 ^ (prefixWord ++ tailWord_4027424).sum := by decide
  have hdescent : baseEnd_4027424 < baseStart_4027424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027450 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_4027450 : Nat := 118140960795 + 4027450 * 2 ^ 59
def prefixEnd_4027450 : Nat := 4983230072969 + 3 ^ 40 * 4027450 * 2
def baseEnd_4027450 : Nat := 1378678441300248544702067

theorem tailTrace_4027450 : CollatzResearch.WordTrace tailWord_4027450 prefixEnd_4027450 1378678441300248544702067 := by
  unfold tailWord_4027450
  simp only [CollatzResearch.WordTrace]
  refine ⟨36723292314810989635967951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97928779506162639029247869 36723292314810989635967951)
  ·
    refine ⟨55084938472216484453951927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36723292314810989635967951 55084938472216484453951927)
    ·
      refine ⟨82627407708324726680927891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55084938472216484453951927 82627407708324726680927891)
      ·
        refine ⟨123941111562487090021391837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82627407708324726680927891 123941111562487090021391837)
        ·
          refine ⟨46477916835932658758021939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123941111562487090021391837 46477916835932658758021939)
          ·
            refine ⟨69716875253898988137032909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46477916835932658758021939 69716875253898988137032909)
            ·
              refine ⟨26143828220212120551387341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69716875253898988137032909 26143828220212120551387341)
              ·
                refine ⟨9803935582579545206770253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26143828220212120551387341 9803935582579545206770253)
                ·
                  refine ⟨3676475843467329452538845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9803935582579545206770253 3676475843467329452538845)
                  ·
                    refine ⟨1378678441300248544702067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676475843467329452538845 1378678441300248544702067)
                    ·
                      rfl

theorem cell22_4027450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_4027450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027450 prefixEnd_4027450 := by exact prefixLift 4027450
  have htrace : WordTrace (prefixWord ++ tailWord_4027450) baseStart_4027450 baseEnd_4027450 := by
    simpa [prefixWord, tailWord_4027450, baseEnd_4027450] using wordTrace_append hprefix tailTrace_4027450
  have hstable : (prefixWord ++ tailWord_4027450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027450).length < 2 ^ (prefixWord ++ tailWord_4027450).sum := by decide
  have hdescent : baseEnd_4027450 < baseStart_4027450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027501 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_4027501 : Nat := 118140960795 + 4027501 * 2 ^ 59
def prefixEnd_4027501 : Nat := 4983230072969 + 3 ^ 40 * 4027501 * 2
def baseEnd_4027501 : Nat := 1378695899642501411676911

theorem tailTrace_4027501 : CollatzResearch.WordTrace tailWord_4027501 prefixEnd_4027501 1378695899642501411676911 := by
  unfold tailWord_4027501
  simp only [CollatzResearch.WordTrace]
  refine ⟨146895029382059194253978357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97930019588039462835985571 146895029382059194253978357)
  ·
    refine ⟨13771409004568049461310471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146895029382059194253978357 13771409004568049461310471)
    ·
      refine ⟨20657113506852074191965707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13771409004568049461310471 20657113506852074191965707)
      ·
        refine ⟨30985670260278111287948561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20657113506852074191965707 30985670260278111287948561)
        ·
          refine ⟨23239252695208583465961421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30985670260278111287948561 23239252695208583465961421)
          ·
            refine ⟨8714719760703218799735533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23239252695208583465961421 8714719760703218799735533)
            ·
              refine ⟨3268019910263707049900825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8714719760703218799735533 3268019910263707049900825)
              ·
                refine ⟨2451014932697780287425619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268019910263707049900825 2451014932697780287425619)
                ·
                  refine ⟨3676522399046670431138429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451014932697780287425619 3676522399046670431138429)
                  ·
                    refine ⟨1378695899642501411676911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676522399046670431138429 1378695899642501411676911)
                    ·
                      rfl

theorem cell22_4027501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_4027501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027501 prefixEnd_4027501 := by exact prefixLift 4027501
  have htrace : WordTrace (prefixWord ++ tailWord_4027501) baseStart_4027501 baseEnd_4027501 := by
    simpa [prefixWord, tailWord_4027501, baseEnd_4027501] using wordTrace_append hprefix tailTrace_4027501
  have hstable : (prefixWord ++ tailWord_4027501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027501).length < 2 ^ (prefixWord ++ tailWord_4027501).sum := by decide
  have hdescent : baseEnd_4027501 < baseStart_4027501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027544 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 1, 4]
def baseStart_4027544 : Nat := 118140960795 + 4027544 * 2 ^ 59
def prefixEnd_4027544 : Nat := 4983230072969 + 3 ^ 40 * 4027544 * 2
def baseEnd_4027544 : Nat := 1378710619421263632851779

theorem tailTrace_4027544 : CollatzResearch.WordTrace tailWord_4027544 prefixEnd_4027544 1378710619421263632851779 := by
  unfold tailWord_4027544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73448298860451706298896843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97931065147268941731862457 73448298860451706298896843)
  ·
    refine ⟨110172448290677559448345265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73448298860451706298896843 110172448290677559448345265)
    ·
      refine ⟨82629336218008169586258949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110172448290677559448345265 82629336218008169586258949)
      ·
        refine ⟨15493000540876531797423553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82629336218008169586258949 15493000540876531797423553)
        ·
          refine ⟨11619750405657398848067665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15493000540876531797423553 11619750405657398848067665)
          ·
            refine ⟨8714812804243049136050749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11619750405657398848067665 8714812804243049136050749)
            ·
              refine ⟨3268054801591143426019031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8714812804243049136050749 3268054801591143426019031)
              ·
                refine ⟨4902082202386715139028547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3268054801591143426019031 4902082202386715139028547)
                ·
                  refine ⟨7353123303580072708542821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902082202386715139028547 7353123303580072708542821)
                  ·
                    refine ⟨1378710619421263632851779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353123303580072708542821 1378710619421263632851779)
                    ·
                      rfl

theorem cell22_4027544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_4027544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027544 prefixEnd_4027544 := by exact prefixLift 4027544
  have htrace : WordTrace (prefixWord ++ tailWord_4027544) baseStart_4027544 baseEnd_4027544 := by
    simpa [prefixWord, tailWord_4027544, baseEnd_4027544] using wordTrace_append hprefix tailTrace_4027544
  have hstable : (prefixWord ++ tailWord_4027544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027544).length < 2 ^ (prefixWord ++ tailWord_4027544).sum := by decide
  have hdescent : baseEnd_4027544 < baseStart_4027544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027557 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_4027557 : Nat := 118140960795 + 4027557 * 2 ^ 59
def prefixEnd_4027557 : Nat := 4983230072969 + 3 ^ 40 * 4027557 * 2
def baseEnd_4027557 : Nat := 1378715069586935932276739

theorem tailTrace_4027557 : CollatzResearch.WordTrace tailWord_4027557 prefixEnd_4027557 1378715069586935932276739 := by
  unfold tailWord_4027557
  simp only [CollatzResearch.WordTrace]
  refine ⟨146897071869856315818016925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97931381246570877212011283 146897071869856315818016925)
  ·
    refine ⟨55086401951196118431756347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146897071869856315818016925 55086401951196118431756347)
    ·
      refine ⟨82629602926794177647634521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55086401951196118431756347 82629602926794177647634521)
      ·
        refine ⟨61972202195095633235725891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82629602926794177647634521 61972202195095633235725891)
        ·
          refine ⟨92958303292643449853588837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61972202195095633235725891 92958303292643449853588837)
          ·
            refine ⟨17429681867370646847547907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92958303292643449853588837 17429681867370646847547907)
            ·
              refine ⟨26144522801055970271321861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429681867370646847547907 26144522801055970271321861)
              ·
                refine ⟨4902098025197994425872849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26144522801055970271321861 4902098025197994425872849)
                ·
                  refine ⟨3676573518898495819404637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4902098025197994425872849 3676573518898495819404637)
                  ·
                    refine ⟨1378715069586935932276739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676573518898495819404637 1378715069586935932276739)
                    ·
                      rfl

theorem cell22_4027557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_4027557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027557 prefixEnd_4027557 := by exact prefixLift 4027557
  have htrace : WordTrace (prefixWord ++ tailWord_4027557) baseStart_4027557 baseEnd_4027557 := by
    simpa [prefixWord, tailWord_4027557, baseEnd_4027557] using wordTrace_append hprefix tailTrace_4027557
  have hstable : (prefixWord ++ tailWord_4027557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027557).length < 2 ^ (prefixWord ++ tailWord_4027557).sum := by decide
  have hdescent : baseEnd_4027557 < baseStart_4027557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027559 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 4]
def baseStart_4027559 : Nat := 118140960795 + 4027559 * 2 ^ 59
def prefixEnd_4027559 : Nat := 4983230072969 + 3 ^ 40 * 4027559 * 2
def baseEnd_4027559 : Nat := 459571918075936197908911

theorem tailTrace_4027559 : CollatzResearch.WordTrace tailWord_4027559 prefixEnd_4027559 459571918075936197908911 := by
  unfold tailWord_4027559
  simp only [CollatzResearch.WordTrace]
  refine ⟨146897144815849070159589731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97931429877232713439726487 146897144815849070159589731)
  ·
    refine ⟨220345717223773605239384597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146897144815849070159589731 220345717223773605239384597)
    ·
      refine ⟨10328705494864387745596153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220345717223773605239384597 10328705494864387745596153)
      ·
        refine ⟨7746529121148290809197115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10328705494864387745596153 7746529121148290809197115)
        ·
          refine ⟨11619793681722436213795673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746529121148290809197115 11619793681722436213795673)
          ·
            refine ⟨8714845261291827160346755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11619793681722436213795673 8714845261291827160346755)
            ·
              refine ⟨13072267891937740740520133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714845261291827160346755 13072267891937740740520133)
              ·
                refine ⟨2451050229738326388847525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13072267891937740740520133 2451050229738326388847525)
                ·
                  refine ⟨459571918075936197908911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451050229738326388847525 459571918075936197908911)
                  ·
                    rfl

theorem cell22_4027559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 4].length) (baseStart_4027559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027559 prefixEnd_4027559 := by exact prefixLift 4027559
  have htrace : WordTrace (prefixWord ++ tailWord_4027559) baseStart_4027559 baseEnd_4027559 := by
    simpa [prefixWord, tailWord_4027559, baseEnd_4027559] using wordTrace_append hprefix tailTrace_4027559
  have hstable : (prefixWord ++ tailWord_4027559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027559).length < 2 ^ (prefixWord ++ tailWord_4027559).sum := by decide
  have hdescent : baseEnd_4027559 < baseStart_4027559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027570 : List Nat := [3, 2, 1, 1, 1, 4, 3, 7]
def baseStart_4027570 : Nat := 118140960795 + 4027570 * 2 ^ 59
def prefixEnd_4027570 : Nat := 4983230072969 + 3 ^ 40 * 4027570 * 2
def baseEnd_4027570 : Nat := 153191057750289803522411

theorem tailTrace_4027570 : CollatzResearch.WordTrace tailWord_4027570 prefixEnd_4027570 153191057750289803522411 := by
  unfold tailWord_4027570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724386504702304759560041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97931697345872812692160109 36724386504702304759560041)
  ·
    refine ⟨27543289878526728569670031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36724386504702304759560041 27543289878526728569670031)
    ·
      refine ⟨41314934817790092854505047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27543289878526728569670031 41314934817790092854505047)
      ·
        refine ⟨61972402226685139281757571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41314934817790092854505047 61972402226685139281757571)
        ·
          refine ⟨92958603340027708922636357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61972402226685139281757571 92958603340027708922636357)
          ·
            refine ⟨17429738126255195422994317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92958603340027708922636357 17429738126255195422994317)
            ·
              refine ⟨6536151797345698283622869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17429738126255195422994317 6536151797345698283622869)
              ·
                refine ⟨153191057750289803522411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6536151797345698283622869 153191057750289803522411)
                ·
                  rfl

theorem cell22_4027570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_4027570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027570 prefixEnd_4027570 := by exact prefixLift 4027570
  have htrace : WordTrace (prefixWord ++ tailWord_4027570) baseStart_4027570 baseEnd_4027570 := by
    simpa [prefixWord, tailWord_4027570, baseEnd_4027570] using wordTrace_append hprefix tailTrace_4027570
  have hstable : (prefixWord ++ tailWord_4027570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027570).length < 2 ^ (prefixWord ++ tailWord_4027570).sum := by decide
  have hdescent : baseEnd_4027570 < baseStart_4027570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027602 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_4027602 : Nat := 118140960795 + 4027602 * 2 ^ 59
def prefixEnd_4027602 : Nat := 4983230072969 + 3 ^ 40 * 4027602 * 2
def baseEnd_4027602 : Nat := 1378730474006570814901601

theorem tailTrace_4027602 : CollatzResearch.WordTrace tailWord_4027602 prefixEnd_4027602 1378730474006570814901601 := by
  unfold tailWord_4027602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724678288673322125851265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97932475436462192335603373 36724678288673322125851265)
  ·
    refine ⟨27543508716504991594388449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36724678288673322125851265 27543508716504991594388449)
    ·
      refine ⟨20657631537378743695791337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27543508716504991594388449 20657631537378743695791337)
      ·
        refine ⟨15493223653034057771843503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20657631537378743695791337 15493223653034057771843503)
        ·
          refine ⟨23239835479551086657765255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15493223653034057771843503 23239835479551086657765255)
          ·
            refine ⟨34859753219326629986647883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23239835479551086657765255 34859753219326629986647883)
            ·
              refine ⟨52289629828989944979971825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34859753219326629986647883 52289629828989944979971825)
              ·
                refine ⟨39217222371742458734978869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52289629828989944979971825 39217222371742458734978869)
                ·
                  refine ⟨3676614597350855506404269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39217222371742458734978869 3676614597350855506404269)
                  ·
                    refine ⟨1378730474006570814901601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676614597350855506404269 1378730474006570814901601)
                    ·
                      rfl

theorem cell22_4027602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_4027602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027602 prefixEnd_4027602 := by exact prefixLift 4027602
  have htrace : WordTrace (prefixWord ++ tailWord_4027602) baseStart_4027602 baseEnd_4027602 := by
    simpa [prefixWord, tailWord_4027602, baseEnd_4027602] using wordTrace_append hprefix tailTrace_4027602
  have hstable : (prefixWord ++ tailWord_4027602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027602).length < 2 ^ (prefixWord ++ tailWord_4027602).sum := by decide
  have hdescent : baseEnd_4027602 < baseStart_4027602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027758 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_4027758 : Nat := 118140960795 + 4027758 * 2 ^ 59
def prefixEnd_4027758 : Nat := 4983230072969 + 3 ^ 40 * 4027758 * 2
def baseEnd_4027758 : Nat := 1378783875994638408001123

theorem tailTrace_4027758 : CollatzResearch.WordTrace tailWord_4027758 prefixEnd_4027758 1378783875994638408001123 := by
  unfold tailWord_4027758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363050367766015893260491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97936268628085418097389285 18363050367766015893260491)
  ·
    refine ⟨27544575551649023839890737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363050367766015893260491 27544575551649023839890737)
    ·
      refine ⟨20658431663736767879918053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27544575551649023839890737 20658431663736767879918053)
      ·
        refine ⟨3873455936950643977484635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20658431663736767879918053 3873455936950643977484635)
        ·
          refine ⟨5810183905425965966226953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873455936950643977484635 5810183905425965966226953)
          ·
            refine ⟨4357637929069474474670215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810183905425965966226953 4357637929069474474670215)
            ·
              refine ⟨6536456893604211712005323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357637929069474474670215 6536456893604211712005323)
              ·
                refine ⟨9804685340406317568007985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6536456893604211712005323 9804685340406317568007985)
                ·
                  refine ⟨7353514005304738176005989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9804685340406317568007985 7353514005304738176005989)
                  ·
                    refine ⟨1378783875994638408001123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353514005304738176005989 1378783875994638408001123)
                    ·
                      rfl

theorem cell22_4027758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_4027758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027758 prefixEnd_4027758 := by exact prefixLift 4027758
  have htrace : WordTrace (prefixWord ++ tailWord_4027758) baseStart_4027758 baseEnd_4027758 := by
    simpa [prefixWord, tailWord_4027758, baseEnd_4027758] using wordTrace_append hprefix tailTrace_4027758
  have hstable : (prefixWord ++ tailWord_4027758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027758).length < 2 ^ (prefixWord ++ tailWord_4027758).sum := by decide
  have hdescent : baseEnd_4027758 < baseStart_4027758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027771 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 1, 3]
def baseStart_4027771 : Nat := 118140960795 + 4027771 * 2 ^ 59
def prefixEnd_4027771 : Nat := 4983230072969 + 3 ^ 40 * 4027771 * 2
def baseEnd_4027771 : Nat := 1378788326160310707426083

theorem tailTrace_4027771 : CollatzResearch.WordTrace tailWord_4027771 prefixEnd_4027771 1378788326160310707426083 := by
  unfold tailWord_4027771
  simp only [CollatzResearch.WordTrace]
  refine ⟨146904877091081030366307167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97936584727387353577538111 146904877091081030366307167)
  ·
    refine ⟨220357315636621545549460751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146904877091081030366307167 220357315636621545549460751)
    ·
      refine ⟨330535973454932318324191127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220357315636621545549460751 330535973454932318324191127)
      ·
        refine ⟨495803960182398477486286691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330535973454932318324191127 495803960182398477486286691)
        ·
          refine ⟨743705940273597716229430037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495803960182398477486286691 743705940273597716229430037)
          ·
            refine ⟨34861215950324892948254533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 743705940273597716229430037 34861215950324892948254533)
            ·
              refine ⟨6536477990685917427797725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34861215950324892948254533 6536477990685917427797725)
              ·
                refine ⟨2451179246507219035424147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6536477990685917427797725 2451179246507219035424147)
                ·
                  refine ⟨3676768869760828553136221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451179246507219035424147 3676768869760828553136221)
                  ·
                    refine ⟨1378788326160310707426083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676768869760828553136221 1378788326160310707426083)
                    ·
                      rfl

theorem cell22_4027771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 3].length) (baseStart_4027771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027771 prefixEnd_4027771 := by exact prefixLift 4027771
  have htrace : WordTrace (prefixWord ++ tailWord_4027771) baseStart_4027771 baseEnd_4027771 := by
    simpa [prefixWord, tailWord_4027771, baseEnd_4027771] using wordTrace_append hprefix tailTrace_4027771
  have hstable : (prefixWord ++ tailWord_4027771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027771).length < 2 ^ (prefixWord ++ tailWord_4027771).sum := by decide
  have hdescent : baseEnd_4027771 < baseStart_4027771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027784 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_4027784 : Nat := 118140960795 + 4027784 * 2 ^ 59
def prefixEnd_4027784 : Nat := 4983230072969 + 3 ^ 40 * 4027784 * 2
def baseEnd_4027784 : Nat := 459597592108661002283681

theorem tailTrace_4027784 : CollatzResearch.WordTrace tailWord_4027784 prefixEnd_4027784 459597592108661002283681 := by
  unfold tailWord_4027784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73452675620016966793265203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97936900826689289057686937 73452675620016966793265203)
  ·
    refine ⟨110179013430025450189897805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73452675620016966793265203 110179013430025450189897805)
    ·
      refine ⟨41317130036259543821211677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110179013430025450189897805 41317130036259543821211677)
      ·
        refine ⟨15493923763597328932954379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41317130036259543821211677 15493923763597328932954379)
        ·
          refine ⟨23240885645395993399431569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15493923763597328932954379 23240885645395993399431569)
          ·
            refine ⟨17430664234046995049573677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23240885645395993399431569 17430664234046995049573677)
            ·
              refine ⟨6536499087767623143590129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17430664234046995049573677 6536499087767623143590129)
              ·
                refine ⟨4902374315825717357692597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536499087767623143590129 4902374315825717357692597)
                ·
                  refine ⟨459597592108661002283681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4902374315825717357692597 459597592108661002283681)
                  ·
                    rfl

theorem cell22_4027784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_4027784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027784 prefixEnd_4027784 := by exact prefixLift 4027784
  have htrace : WordTrace (prefixWord ++ tailWord_4027784) baseStart_4027784 baseEnd_4027784 := by
    simpa [prefixWord, tailWord_4027784, baseEnd_4027784] using wordTrace_append hprefix tailTrace_4027784
  have hstable : (prefixWord ++ tailWord_4027784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027784).length < 2 ^ (prefixWord ++ tailWord_4027784).sum := by decide
  have hdescent : baseEnd_4027784 < baseStart_4027784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027797 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_4027797 : Nat := 118140960795 + 4027797 * 2 ^ 59
def prefixEnd_4027797 : Nat := 4983230072969 + 3 ^ 40 * 4027797 * 2
def baseEnd_4027797 : Nat := 1378797226491655306276003

theorem tailTrace_4027797 : CollatzResearch.WordTrace tailWord_4027797 prefixEnd_4027797 1378797226491655306276003 := by
  unfold tailWord_4027797
  simp only [CollatzResearch.WordTrace]
  refine ⟨146905825388986836806753645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97937216925991224537835763 146905825388986836806753645)
  ·
    refine ⟨55089684520870063802532617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146905825388986836806753645 55089684520870063802532617)
    ·
      refine ⟨41317263390652547851899463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55089684520870063802532617 41317263390652547851899463)
      ·
        refine ⟨61975895085978821777849195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41317263390652547851899463 61975895085978821777849195)
        ·
          refine ⟨92963842628968232666773793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61975895085978821777849195 92963842628968232666773793)
          ·
            refine ⟨69722881971726174500080345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92963842628968232666773793 69722881971726174500080345)
            ·
              refine ⟨52292161478794630875060259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69722881971726174500080345 52292161478794630875060259)
              ·
                refine ⟨78438242218191946312590389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52292161478794630875060259 78438242218191946312590389)
                ·
                  refine ⟨7353585207955494966805349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78438242218191946312590389 7353585207955494966805349)
                  ·
                    refine ⟨1378797226491655306276003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353585207955494966805349 1378797226491655306276003)
                    ·
                      rfl

theorem cell22_4027797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_4027797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027797 prefixEnd_4027797 := by exact prefixLift 4027797
  have htrace : WordTrace (prefixWord ++ tailWord_4027797) baseStart_4027797 baseEnd_4027797 := by
    simpa [prefixWord, tailWord_4027797, baseEnd_4027797] using wordTrace_append hprefix tailTrace_4027797
  have hstable : (prefixWord ++ tailWord_4027797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027797).length < 2 ^ (prefixWord ++ tailWord_4027797).sum := by decide
  have hdescent : baseEnd_4027797 < baseStart_4027797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027827 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 1, 5]
def baseStart_4027827 : Nat := 118140960795 + 4027827 * 2 ^ 59
def prefixEnd_4027827 : Nat := 4983230072969 + 3 ^ 40 * 4027827 * 2
def baseEnd_4027827 : Nat := 1378807496104745228025911

theorem tailTrace_4027827 : CollatzResearch.WordTrace tailWord_4027827 prefixEnd_4027827 1378807496104745228025911 := by
  unfold tailWord_4027827
  simp only [CollatzResearch.WordTrace]
  refine ⟨146906919578878151930345735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97937946385918767953563823 146906919578878151930345735)
  ·
    refine ⟨220360379368317227895518603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146906919578878151930345735 220360379368317227895518603)
    ·
      refine ⟨330540569052475841843277905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220360379368317227895518603 330540569052475841843277905)
      ·
        refine ⟨247905426789356881382458429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330540569052475841843277905 247905426789356881382458429)
        ·
          refine ⟨92964535046008830518421911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247905426789356881382458429 92964535046008830518421911)
          ·
            refine ⟨139446802569013245777632867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92964535046008830518421911 139446802569013245777632867)
            ·
              refine ⟨209170203853519868666449301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139446802569013245777632867 209170203853519868666449301)
              ·
                refine ⟨9804853305633743843739811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209170203853519868666449301 9804853305633743843739811)
                ·
                  refine ⟨14707279958450615765609717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9804853305633743843739811 14707279958450615765609717)
                  ·
                    refine ⟨1378807496104745228025911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14707279958450615765609717 1378807496104745228025911)
                    ·
                      rfl

theorem cell22_4027827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_4027827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027827 prefixEnd_4027827 := by exact prefixLift 4027827
  have htrace : WordTrace (prefixWord ++ tailWord_4027827) baseStart_4027827 baseEnd_4027827 := by
    simpa [prefixWord, tailWord_4027827, baseEnd_4027827] using wordTrace_append hprefix tailTrace_4027827
  have hstable : (prefixWord ++ tailWord_4027827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027827).length < 2 ^ (prefixWord ++ tailWord_4027827).sum := by decide
  have hdescent : baseEnd_4027827 < baseStart_4027827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027861 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_4027861 : Nat := 118140960795 + 4027861 * 2 ^ 59
def prefixEnd_4027861 : Nat := 4983230072969 + 3 ^ 40 * 4027861 * 2
def baseEnd_4027861 : Nat := 1378819134999580472675807

theorem tailTrace_4027861 : CollatzResearch.WordTrace tailWord_4027861 prefixEnd_4027861 1378819134999580472675807 := by
  unfold tailWord_4027861
  simp only [CollatzResearch.WordTrace]
  refine ⟨146908159660754975737083437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97938773107169983824722291 146908159660754975737083437)
  ·
    refine ⟨55090559872783115901406289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146908159660754975737083437 55090559872783115901406289)
    ·
      refine ⟨41317919904587336926054717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55090559872783115901406289 41317919904587336926054717)
      ·
        refine ⟨15494219964220251347270519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41317919904587336926054717 15494219964220251347270519)
        ·
          refine ⟨23241329946330377020905779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15494219964220251347270519 23241329946330377020905779)
          ·
            refine ⟨34861994919495565531358669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23241329946330377020905779 34861994919495565531358669)
            ·
              refine ⟨13073248094810837074259501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34861994919495565531358669 13073248094810837074259501)
              ·
                refine ⟨4902468035554063902847313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13073248094810837074259501 4902468035554063902847313)
                ·
                  refine ⟨3676851026665547927135485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4902468035554063902847313 3676851026665547927135485)
                  ·
                    refine ⟨1378819134999580472675807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676851026665547927135485 1378819134999580472675807)
                    ·
                      rfl

theorem cell22_4027861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_4027861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027861 prefixEnd_4027861 := by exact prefixLift 4027861
  have htrace : WordTrace (prefixWord ++ tailWord_4027861) baseStart_4027861 baseEnd_4027861 := by
    simpa [prefixWord, tailWord_4027861, baseEnd_4027861] using wordTrace_append hprefix tailTrace_4027861
  have hstable : (prefixWord ++ tailWord_4027861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027861).length < 2 ^ (prefixWord ++ tailWord_4027861).sum := by decide
  have hdescent : baseEnd_4027861 < baseStart_4027861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027908 : List Nat := [2, 3, 2, 3, 3, 1, 1, 7]
def baseStart_4027908 : Nat := 118140960795 + 4027908 * 2 ^ 59
def prefixEnd_4027908 : Nat := 4983230072969 + 3 ^ 40 * 4027908 * 2
def baseEnd_4027908 : Nat := 153203913784454224083407

theorem tailTrace_4027908 : CollatzResearch.WordTrace tailWord_4027908 prefixEnd_4027908 153203913784454224083407 := by
  unfold tailWord_4027908
  simp only [CollatzResearch.WordTrace]
  refine ⟨73454936945792351382022189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97939915927723135176029585 73454936945792351382022189)
  ·
    refine ⟨27545601354672131768258321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73454936945792351382022189 27545601354672131768258321)
    ·
      refine ⟨20659201016004098826193741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27545601354672131768258321 20659201016004098826193741)
      ·
        refine ⟨7747200381001537059822653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20659201016004098826193741 7747200381001537059822653)
        ·
          refine ⟨2905200142875576397433495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7747200381001537059822653 2905200142875576397433495)
          ·
            refine ⟨4357800214313364596150243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905200142875576397433495 4357800214313364596150243)
            ·
              refine ⟨6536700321470046894225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357800214313364596150243 6536700321470046894225365)
              ·
                refine ⟨153203913784454224083407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6536700321470046894225365 153203913784454224083407)
                ·
                  rfl

theorem cell22_4027908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 7].length) (baseStart_4027908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027908 prefixEnd_4027908 := by exact prefixLift 4027908
  have htrace : WordTrace (prefixWord ++ tailWord_4027908) baseStart_4027908 baseEnd_4027908 := by
    simpa [prefixWord, tailWord_4027908, baseEnd_4027908] using wordTrace_append hprefix tailTrace_4027908
  have hstable : (prefixWord ++ tailWord_4027908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027908).length < 2 ^ (prefixWord ++ tailWord_4027908).sum := by decide
  have hdescent : baseEnd_4027908 < baseStart_4027908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027994 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_4027994 : Nat := 118140960795 + 4027994 * 2 ^ 59
def prefixEnd_4027994 : Nat := 4983230072969 + 3 ^ 40 * 4027994 * 2
def baseEnd_4027994 : Nat := 1378864663617612459100399

theorem tailTrace_4027994 : CollatzResearch.WordTrace tailWord_4027994 prefixEnd_4027994 1378864663617612459100399 := by
  unfold tailWord_4027994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728252642318284862918759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97942007046182092967783357 36728252642318284862918759)
  ·
    refine ⟨55092378963477427294378139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36728252642318284862918759 55092378963477427294378139)
    ·
      refine ⟨82638568445216140941567209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55092378963477427294378139 82638568445216140941567209)
      ·
        refine ⟨61978926333912105706175407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82638568445216140941567209 61978926333912105706175407)
        ·
          refine ⟨92968389500868158559263111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61978926333912105706175407 92968389500868158559263111)
          ·
            refine ⟨139452584251302237838894667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92968389500868158559263111 139452584251302237838894667)
            ·
              refine ⟨209178876376953356758342001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139452584251302237838894667 209178876376953356758342001)
              ·
                refine ⟨156884157282715017568756501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209178876376953356758342001 156884157282715017568756501)
                ·
                  refine ⟨7353944872627266448535461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156884157282715017568756501 7353944872627266448535461)
                  ·
                    refine ⟨1378864663617612459100399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7353944872627266448535461 1378864663617612459100399)
                    ·
                      rfl

theorem cell22_4027994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_4027994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4027994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4027994 prefixEnd_4027994 := by exact prefixLift 4027994
  have htrace : WordTrace (prefixWord ++ tailWord_4027994) baseStart_4027994 baseEnd_4027994 := by
    simpa [prefixWord, tailWord_4027994, baseEnd_4027994] using wordTrace_append hprefix tailTrace_4027994
  have hstable : (prefixWord ++ tailWord_4027994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027994).length < 2 ^ (prefixWord ++ tailWord_4027994).sum := by decide
  have hdescent : baseEnd_4027994 < baseStart_4027994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028041 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_4028041 : Nat := 118140960795 + 4028041 * 2 ^ 59
def prefixEnd_4028041 : Nat := 4983230072969 + 3 ^ 40 * 4028041 * 2
def baseEnd_4028041 : Nat := 1378880752678120003175255

theorem tailTrace_4028041 : CollatzResearch.WordTrace tailWord_4028041 prefixEnd_4028041 1378880752678120003175255 := by
  unfold tailWord_4028041
  simp only [CollatzResearch.WordTrace]
  refine ⟨146914724800102866478635977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97943149866735244319090651 146914724800102866478635977)
  ·
    refine ⟨110186043600077149858976983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146914724800102866478635977 110186043600077149858976983)
    ·
      refine ⟨165279065400115724788465475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110186043600077149858976983 165279065400115724788465475)
      ·
        refine ⟨247918598100173587182698213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165279065400115724788465475 247918598100173587182698213)
        ·
          refine ⟨46484737143782547596755915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247918598100173587182698213 46484737143782547596755915)
          ·
            refine ⟨69727105715673821395133873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46484737143782547596755915 69727105715673821395133873)
            ·
              refine ⟨52295329286755366046350405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69727105715673821395133873 52295329286755366046350405)
              ·
                refine ⟨9805374241266631133690701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52295329286755366046350405 9805374241266631133690701)
                ·
                  refine ⟨3677015340474986675134013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9805374241266631133690701 3677015340474986675134013)
                  ·
                    refine ⟨1378880752678120003175255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677015340474986675134013 1378880752678120003175255)
                    ·
                      rfl

theorem cell22_4028041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_4028041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028041 prefixEnd_4028041 := by exact prefixLift 4028041
  have htrace : WordTrace (prefixWord ++ tailWord_4028041) baseStart_4028041 baseEnd_4028041 := by
    simpa [prefixWord, tailWord_4028041, baseEnd_4028041] using wordTrace_append hprefix tailTrace_4028041
  have hstable : (prefixWord ++ tailWord_4028041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028041).length < 2 ^ (prefixWord ++ tailWord_4028041).sum := by decide
  have hdescent : baseEnd_4028041 < baseStart_4028041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028109 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4028109 : Nat := 118140960795 + 4028109 * 2 ^ 59
def prefixEnd_4028109 : Nat := 4983230072969 + 3 ^ 40 * 4028109 * 2
def baseEnd_4028109 : Nat := 1378904030467790492475047

theorem tailTrace_4028109 : CollatzResearch.WordTrace tailWord_4028109 prefixEnd_4028109 1378904030467790492475047 := by
  unfold tailWord_4028109
  simp only [CollatzResearch.WordTrace]
  refine ⟨146917204963856514092111381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97944803309237676061407587 146917204963856514092111381)
  ·
    refine ⟨6886743982680774098067721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146917204963856514092111381 6886743982680774098067721)
    ·
      refine ⟨5165057987010580573550791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6886743982680774098067721 5165057987010580573550791)
      ·
        refine ⟨7747586980515870860326187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165057987010580573550791 7747586980515870860326187)
        ·
          refine ⟨11621380470773806290489281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747586980515870860326187 11621380470773806290489281)
          ·
            refine ⟨8716035353080354717866961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11621380470773806290489281 8716035353080354717866961)
            ·
              refine ⟨6537026514810266038400221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716035353080354717866961 6537026514810266038400221)
              ·
                refine ⟨2451384943053849764400083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6537026514810266038400221 2451384943053849764400083)
                ·
                  refine ⟨3677077414580774646600125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451384943053849764400083 3677077414580774646600125)
                  ·
                    refine ⟨1378904030467790492475047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677077414580774646600125 1378904030467790492475047)
                    ·
                      rfl

theorem cell22_4028109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4028109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028109 prefixEnd_4028109 := by exact prefixLift 4028109
  have htrace : WordTrace (prefixWord ++ tailWord_4028109) baseStart_4028109 baseEnd_4028109 := by
    simpa [prefixWord, tailWord_4028109, baseEnd_4028109] using wordTrace_append hprefix tailTrace_4028109
  have hstable : (prefixWord ++ tailWord_4028109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028109).length < 2 ^ (prefixWord ++ tailWord_4028109).sum := by decide
  have hdescent : baseEnd_4028109 < baseStart_4028109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028133 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 4]
def baseStart_4028133 : Nat := 118140960795 + 4028133 * 2 ^ 59
def prefixEnd_4028133 : Nat := 4983230072969 + 3 ^ 40 * 4028133 * 2
def baseEnd_4028133 : Nat := 459637415386087476624991

theorem tailTrace_4028133 : CollatzResearch.WordTrace tailWord_4028133 prefixEnd_4028133 459637415386087476624991 := by
  unfold tailWord_4028133
  simp only [CollatzResearch.WordTrace]
  refine ⟨146918080315769566190985053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97945386877179710793990035 146918080315769566190985053)
  ·
    refine ⟨55094280118413587321619395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146918080315769566190985053 55094280118413587321619395)
    ·
      refine ⟨82641420177620380982429093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55094280118413587321619395 82641420177620380982429093)
      ·
        refine ⟨15495266283303821434205455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82641420177620380982429093 15495266283303821434205455)
        ·
          refine ⟨23242899424955732151308183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15495266283303821434205455 23242899424955732151308183)
          ·
            refine ⟨34864349137433598226962275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23242899424955732151308183 34864349137433598226962275)
            ·
              refine ⟨52296523706150397340443413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34864349137433598226962275 52296523706150397340443413)
              ·
                refine ⟨2451399548725799875333285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52296523706150397340443413 2451399548725799875333285)
                ·
                  refine ⟨459637415386087476624991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451399548725799875333285 459637415386087476624991)
                  ·
                    rfl

theorem cell22_4028133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_4028133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028133 prefixEnd_4028133 := by exact prefixLift 4028133
  have htrace : WordTrace (prefixWord ++ tailWord_4028133) baseStart_4028133 baseEnd_4028133 := by
    simpa [prefixWord, tailWord_4028133, baseEnd_4028133] using wordTrace_append hprefix tailTrace_4028133
  have hstable : (prefixWord ++ tailWord_4028133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028133).length < 2 ^ (prefixWord ++ tailWord_4028133).sum := by decide
  have hdescent : baseEnd_4028133 < baseStart_4028133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028146 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_4028146 : Nat := 118140960795 + 4028146 * 2 ^ 59
def prefixEnd_4028146 : Nat := 4983230072969 + 3 ^ 40 * 4028146 * 2
def baseEnd_4028146 : Nat := 1378916696323934729299933

theorem tailTrace_4028146 : CollatzResearch.WordTrace tailWord_4028146 prefixEnd_4028146 1378916696323934729299933 := by
  unfold tailWord_4028146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36729638616180617352802073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97945702976481646274138861 36729638616180617352802073)
  ·
    refine ⟨27547228962135463014601555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36729638616180617352802073 27547228962135463014601555)
    ·
      refine ⟨41320843443203194521902333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27547228962135463014601555 41320843443203194521902333)
      ·
        refine ⟨15495316291201197945713375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41320843443203194521902333 15495316291201197945713375)
        ·
          refine ⟨23242974436801796918570063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15495316291201197945713375 23242974436801796918570063)
          ·
            refine ⟨34864461655202695377855095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23242974436801796918570063 34864461655202695377855095)
            ·
              refine ⟨52296692482804043066782643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34864461655202695377855095 52296692482804043066782643)
              ·
                refine ⟨78445038724206064600173965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52296692482804043066782643 78445038724206064600173965)
                ·
                  refine ⟨29416889521577274225065237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78445038724206064600173965 29416889521577274225065237)
                  ·
                    refine ⟨1378916696323934729299933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29416889521577274225065237 1378916696323934729299933)
                    ·
                      rfl

theorem cell22_4028146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_4028146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028146 prefixEnd_4028146 := by exact prefixLift 4028146
  have htrace : WordTrace (prefixWord ++ tailWord_4028146) baseStart_4028146 baseEnd_4028146 := by
    simpa [prefixWord, tailWord_4028146, baseEnd_4028146] using wordTrace_append hprefix tailTrace_4028146
  have hstable : (prefixWord ++ tailWord_4028146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028146).length < 2 ^ (prefixWord ++ tailWord_4028146).sum := by decide
  have hdescent : baseEnd_4028146 < baseStart_4028146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028167 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 4]
def baseStart_4028167 : Nat := 118140960795 + 4028167 * 2 ^ 59
def prefixEnd_4028167 : Nat := 4983230072969 + 3 ^ 40 * 4028167 * 2
def baseEnd_4028167 : Nat := 459641295017699224841623

theorem tailTrace_4028167 : CollatzResearch.WordTrace tailWord_4028167 prefixEnd_4028167 459641295017699224841623 := by
  unfold tailWord_4028167
  simp only [CollatzResearch.WordTrace]
  refine ⟨146919320397646389997722755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97946213598430926665148503 146919320397646389997722755)
  ·
    refine ⟨220378980596469584996584133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146919320397646389997722755 220378980596469584996584133)
    ·
      refine ⟨41321058861838047186859525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220378980596469584996584133 41321058861838047186859525)
      ·
        refine ⟨7747698536594633847536161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41321058861838047186859525 7747698536594633847536161)
        ·
          refine ⟨5810773902445975385652121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7747698536594633847536161 5810773902445975385652121)
          ·
            refine ⟨4358080426834481539239091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810773902445975385652121 4358080426834481539239091)
            ·
              refine ⟨6537120640251722308858637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358080426834481539239091 6537120640251722308858637)
              ·
                refine ⟨2451420240094395865821989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6537120640251722308858637 2451420240094395865821989)
                ·
                  refine ⟨459641295017699224841623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451420240094395865821989 459641295017699224841623)
                  ·
                    rfl

theorem cell22_4028167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 4].length) (baseStart_4028167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028167 prefixEnd_4028167 := by exact prefixLift 4028167
  have htrace : WordTrace (prefixWord ++ tailWord_4028167) baseStart_4028167 baseEnd_4028167 := by
    simpa [prefixWord, tailWord_4028167, baseEnd_4028167] using wordTrace_append hprefix tailTrace_4028167
  have hstable : (prefixWord ++ tailWord_4028167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028167).length < 2 ^ (prefixWord ++ tailWord_4028167).sum := by decide
  have hdescent : baseEnd_4028167 < baseStart_4028167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028178 : List Nat := [3, 2, 4, 1, 1, 1, 10]
def baseStart_4028178 : Nat := 118140960795 + 4028178 * 2 ^ 59
def prefixEnd_4028178 : Nat := 4983230072969 + 3 ^ 40 * 4028178 * 2
def baseEnd_4028178 : Nat := 51071394465848048611105

theorem tailTrace_4028178 : CollatzResearch.WordTrace tailWord_4028178 prefixEnd_4028178 51071394465848048611105 := by
  unfold tailWord_4028178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36729930400151634719093297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97946481067071025917582125 36729930400151634719093297)
  ·
    refine ⟨27547447800113726039319973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36729930400151634719093297 27547447800113726039319973)
    ·
      refine ⟨5165146462521323632372495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27547447800113726039319973 5165146462521323632372495)
      ·
        refine ⟨7747719693781985448558743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165146462521323632372495 7747719693781985448558743)
        ·
          refine ⟨11621579540672978172838115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747719693781985448558743 11621579540672978172838115)
          ·
            refine ⟨17432369311009467259257173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621579540672978172838115 17432369311009467259257173)
            ·
              refine ⟨51071394465848048611105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17432369311009467259257173 51071394465848048611105)
              ·
                rfl

theorem cell22_4028178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 10].length) (baseStart_4028178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028178 prefixEnd_4028178 := by exact prefixLift 4028178
  have htrace : WordTrace (prefixWord ++ tailWord_4028178) baseStart_4028178 baseEnd_4028178 := by
    simpa [prefixWord, tailWord_4028178, baseEnd_4028178] using wordTrace_append hprefix tailTrace_4028178
  have hstable : (prefixWord ++ tailWord_4028178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028178).length < 2 ^ (prefixWord ++ tailWord_4028178).sum := by decide
  have hdescent : baseEnd_4028178 < baseStart_4028178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028191 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_4028191 : Nat := 118140960795 + 4028191 * 2 ^ 59
def prefixEnd_4028191 : Nat := 4983230072969 + 3 ^ 40 * 4028191 * 2
def baseEnd_4028191 : Nat := 1378932100743569611924795

theorem tailTrace_4028191 : CollatzResearch.WordTrace tailWord_4028191 prefixEnd_4028191 1378932100743569611924795 := by
  unfold tailWord_4028191
  simp only [CollatzResearch.WordTrace]
  refine ⟨146920195749559442096596427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97946797166372961397730951 146920195749559442096596427)
  ·
    refine ⟨220380293624339163144894641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146920195749559442096596427 220380293624339163144894641)
    ·
      refine ⟨165285220218254372358670981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220380293624339163144894641 165285220218254372358670981)
      ·
        refine ⟨30990978790922694817250809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165285220218254372358670981 30990978790922694817250809)
        ·
          refine ⟨23243234093192021112938107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30990978790922694817250809 23243234093192021112938107)
          ·
            refine ⟨34864851139788031669407161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23243234093192021112938107 34864851139788031669407161)
            ·
              refine ⟨26148638354841023752055371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34864851139788031669407161 26148638354841023752055371)
              ·
                refine ⟨39222957532261535628083057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26148638354841023752055371 39222957532261535628083057)
                ·
                  refine ⟨29417218149196151721062293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39222957532261535628083057 29417218149196151721062293)
                  ·
                    refine ⟨1378932100743569611924795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29417218149196151721062293 1378932100743569611924795)
                    ·
                      rfl

theorem cell22_4028191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_4028191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028191 prefixEnd_4028191 := by exact prefixLift 4028191
  have htrace : WordTrace (prefixWord ++ tailWord_4028191) baseStart_4028191 baseEnd_4028191 := by
    simpa [prefixWord, tailWord_4028191, baseEnd_4028191] using wordTrace_append hprefix tailTrace_4028191
  have hstable : (prefixWord ++ tailWord_4028191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028191).length < 2 ^ (prefixWord ++ tailWord_4028191).sum := by decide
  have hdescent : baseEnd_4028191 < baseStart_4028191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028244 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_4028244 : Nat := 118140960795 + 4028244 * 2 ^ 59
def prefixEnd_4028244 : Nat := 4983230072969 + 3 ^ 40 * 4028244 * 2
def baseEnd_4028244 : Nat := 1378950243726695140349633

theorem tailTrace_4028244 : CollatzResearch.WordTrace tailWord_4028244 prefixEnd_4028244 1378950243726695140349633 := by
  unfold tailWord_4028244
  simp only [CollatzResearch.WordTrace]
  refine ⟨73461064409183716074137893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97948085878911621432183857 73461064409183716074137893)
  ·
    refine ⟨13773949576721946763900855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73461064409183716074137893 13773949576721946763900855)
    ·
      refine ⟨20660924365082920145851283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13773949576721946763900855 20660924365082920145851283)
      ·
        refine ⟨30991386547624380218776925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20660924365082920145851283 30991386547624380218776925)
        ·
          refine ⟨11621769955359142582041347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30991386547624380218776925 11621769955359142582041347)
          ·
            refine ⟨17432654933038713873062021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621769955359142582041347 17432654933038713873062021)
            ·
              refine ⟨3268622799944758851199129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17432654933038713873062021 3268622799944758851199129)
              ·
                refine ⟨2451467099958569138399347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268622799944758851199129 2451467099958569138399347)
                ·
                  refine ⟨3677200649937853707599021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451467099958569138399347 3677200649937853707599021)
                  ·
                    refine ⟨1378950243726695140349633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677200649937853707599021 1378950243726695140349633)
                    ·
                      rfl

theorem cell22_4028244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_4028244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028244 prefixEnd_4028244 := by exact prefixLift 4028244
  have htrace : WordTrace (prefixWord ++ tailWord_4028244) baseStart_4028244 baseEnd_4028244 := by
    simpa [prefixWord, tailWord_4028244, baseEnd_4028244] using wordTrace_append hprefix tailTrace_4028244
  have hstable : (prefixWord ++ tailWord_4028244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028244).length < 2 ^ (prefixWord ++ tailWord_4028244).sum := by decide
  have hdescent : baseEnd_4028244 < baseStart_4028244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028268 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_4028268 : Nat := 118140960795 + 4028268 * 2 ^ 59
def prefixEnd_4028268 : Nat := 4983230072969 + 3 ^ 40 * 4028268 * 2
def baseEnd_4028268 : Nat := 459652819805722359249853

theorem tailTrace_4028268 : CollatzResearch.WordTrace tailWord_4028268 prefixEnd_4028268 459652819805722359249853 := by
  unfold tailWord_4028268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73461502085140242123574729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97948669446853656164766305 73461502085140242123574729)
  ·
    refine ⟨55096126563855181592681047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73461502085140242123574729 55096126563855181592681047)
    ·
      refine ⟨82644189845782772389021571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55096126563855181592681047 82644189845782772389021571)
      ·
        refine ⟨123966284768674158583532357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82644189845782772389021571 123966284768674158583532357)
        ·
          refine ⟨23243678394126404734412317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123966284768674158583532357 23243678394126404734412317)
          ·
            refine ⟨8716379397797401775404619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23243678394126404734412317 8716379397797401775404619)
            ·
              refine ⟨13074569096696102663106929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716379397797401775404619 13074569096696102663106929)
              ·
                refine ⟨9805926822522076997330197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13074569096696102663106929 9805926822522076997330197)
                ·
                  refine ⟨459652819805722359249853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9805926822522076997330197 459652819805722359249853)
                  ·
                    rfl

theorem cell22_4028268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_4028268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028268 prefixEnd_4028268 := by exact prefixLift 4028268
  have htrace : WordTrace (prefixWord ++ tailWord_4028268) baseStart_4028268 baseEnd_4028268 := by
    simpa [prefixWord, tailWord_4028268, baseEnd_4028268] using wordTrace_append hprefix tailTrace_4028268
  have hstable : (prefixWord ++ tailWord_4028268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028268).length < 2 ^ (prefixWord ++ tailWord_4028268).sum := by decide
  have hdescent : baseEnd_4028268 < baseStart_4028268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028270 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_4028270 : Nat := 118140960795 + 4028270 * 2 ^ 59
def prefixEnd_4028270 : Nat := 4983230072969 + 3 ^ 40 * 4028270 * 2
def baseEnd_4028270 : Nat := 1378959144058039739199553

theorem tailTrace_4028270 : CollatzResearch.WordTrace tailWord_4028270 prefixEnd_4028270 1378959144058039739199553 := by
  unfold tailWord_4028270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18365384639534154823590283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97948718077515492392481509 18365384639534154823590283)
  ·
    refine ⟨27548076959301232235385425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18365384639534154823590283 27548076959301232235385425)
    ·
      refine ⟨20661057719475924176539069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27548076959301232235385425 20661057719475924176539069)
      ·
        refine ⟨7747896644803471566202151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20661057719475924176539069 7747896644803471566202151)
        ·
          refine ⟨11621844967205207349303227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747896644803471566202151 11621844967205207349303227)
          ·
            refine ⟨17432767450807811023954841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621844967205207349303227 17432767450807811023954841)
            ·
              refine ⟨13074575588105858267966131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17432767450807811023954841 13074575588105858267966131)
              ·
                refine ⟨19611863382158787401949197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074575588105858267966131 19611863382158787401949197)
                ·
                  refine ⟨7354448768309545275730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19611863382158787401949197 7354448768309545275730949)
                  ·
                    refine ⟨1378959144058039739199553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7354448768309545275730949 1378959144058039739199553)
                    ·
                      rfl

theorem cell22_4028270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_4028270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028270 prefixEnd_4028270 := by exact prefixLift 4028270
  have htrace : WordTrace (prefixWord ++ tailWord_4028270) baseStart_4028270 baseEnd_4028270 := by
    simpa [prefixWord, tailWord_4028270, baseEnd_4028270] using wordTrace_append hprefix tailTrace_4028270
  have hstable : (prefixWord ++ tailWord_4028270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028270).length < 2 ^ (prefixWord ++ tailWord_4028270).sum := by decide
  have hdescent : baseEnd_4028270 < baseStart_4028270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028283 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 4, 3]
def baseStart_4028283 : Nat := 118140960795 + 4028283 * 2 ^ 59
def prefixEnd_4028283 : Nat := 4983230072969 + 3 ^ 40 * 4028283 * 2
def baseEnd_4028283 : Nat := 1378963594223712038624513

theorem tailTrace_4028283 : CollatzResearch.WordTrace tailWord_4028283 prefixEnd_4028283 1378963594223712038624513 := by
  unfold tailWord_4028283
  simp only [CollatzResearch.WordTrace]
  refine ⟨146923551265226141808945503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97949034176817427872630335 146923551265226141808945503)
  ·
    refine ⟨220385326897839212713418255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146923551265226141808945503 220385326897839212713418255)
    ·
      refine ⟨330577990346758819070127383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220385326897839212713418255 330577990346758819070127383)
      ·
        refine ⟨495866985520138228605191075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330577990346758819070127383 495866985520138228605191075)
        ·
          refine ⟨743800478280207342907786613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495866985520138228605191075 743800478280207342907786613)
          ·
            refine ⟨69731294838769438397604995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 743800478280207342907786613 69731294838769438397604995)
            ·
              refine ⟨104596942258154157596407493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69731294838769438397604995 104596942258154157596407493)
              ·
                refine ⟨19611926673403904549326405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104596942258154157596407493 19611926673403904549326405)
                ·
                  refine ⟨3677236251263232102998701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19611926673403904549326405 3677236251263232102998701)
                  ·
                    refine ⟨1378963594223712038624513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677236251263232102998701 1378963594223712038624513)
                    ·
                      rfl

theorem cell22_4028283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 3].length) (baseStart_4028283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028283 prefixEnd_4028283 := by exact prefixLift 4028283
  have htrace : WordTrace (prefixWord ++ tailWord_4028283) baseStart_4028283 baseEnd_4028283 := by
    simpa [prefixWord, tailWord_4028283, baseEnd_4028283] using wordTrace_append hprefix tailTrace_4028283
  have hstable : (prefixWord ++ tailWord_4028283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028283).length < 2 ^ (prefixWord ++ tailWord_4028283).sum := by decide
  have hdescent : baseEnd_4028283 < baseStart_4028283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028302 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_4028302 : Nat := 118140960795 + 4028302 * 2 ^ 59
def prefixEnd_4028302 : Nat := 4983230072969 + 3 ^ 40 * 4028302 * 2
def baseEnd_4028302 : Nat := 459656699437334107466485

theorem tailTrace_4028302 : CollatzResearch.WordTrace tailWord_4028302 prefixEnd_4028302 459656699437334107466485 := by
  unfold tailWord_4028302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18365530531519663506735895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97949496168104872035924773 18365530531519663506735895)
  ·
    refine ⟨27548295797279495260103843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18365530531519663506735895 27548295797279495260103843)
    ·
      refine ⟨41322443695919242890155765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27548295797279495260103843 41322443695919242890155765)
      ·
        refine ⟨3873979096492429020952103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41322443695919242890155765 3873979096492429020952103)
        ·
          refine ⟨5810968644738643531428155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873979096492429020952103 5810968644738643531428155)
          ·
            refine ⟨8716452967107965297142233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810968644738643531428155 8716452967107965297142233)
            ·
              refine ⟨6537339725330973972856675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716452967107965297142233 6537339725330973972856675)
              ·
                refine ⟨9806009587996460959285013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537339725330973972856675 9806009587996460959285013)
                ·
                  refine ⟨459656699437334107466485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9806009587996460959285013 459656699437334107466485)
                  ·
                    rfl

theorem cell22_4028302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_4028302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028302 prefixEnd_4028302 := by exact prefixLift 4028302
  have htrace : WordTrace (prefixWord ++ tailWord_4028302) baseStart_4028302 baseEnd_4028302 := by
    simpa [prefixWord, tailWord_4028302, baseEnd_4028302] using wordTrace_append hprefix tailTrace_4028302
  have hstable : (prefixWord ++ tailWord_4028302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028302).length < 2 ^ (prefixWord ++ tailWord_4028302).sum := by decide
  have hdescent : baseEnd_4028302 < baseStart_4028302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028362 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_4028362 : Nat := 118140960795 + 4028362 * 2 ^ 59
def prefixEnd_4028362 : Nat := 4983230072969 + 3 ^ 40 * 4028362 * 2
def baseEnd_4028362 : Nat := 1378990637538182165899271

theorem tailTrace_4028362 : CollatzResearch.WordTrace tailWord_4028362 prefixEnd_4028362 1378990637538182165899271 := by
  unfold tailWord_4028362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36731608157984984575267835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97950955087959958867380893 36731608157984984575267835)
  ·
    refine ⟨55097412236977476862901753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36731608157984984575267835 55097412236977476862901753)
    ·
      refine ⟨41323059177733107647176315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55097412236977476862901753 41323059177733107647176315)
      ·
        refine ⟨61984588766599661470764473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41323059177733107647176315 61984588766599661470764473)
        ·
          refine ⟨46488441574949746103073355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61984588766599661470764473 46488441574949746103073355)
          ·
            refine ⟨69732662362424619154610033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46488441574949746103073355 69732662362424619154610033)
            ·
              refine ⟨52299496771818464365957525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69732662362424619154610033 52299496771818464365957525)
              ·
                refine ⟨2451538911178990517154259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52299496771818464365957525 2451538911178990517154259)
                ·
                  refine ⟨3677308366768485775731389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451538911178990517154259 3677308366768485775731389)
                  ·
                    refine ⟨1378990637538182165899271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677308366768485775731389 1378990637538182165899271)
                    ·
                      rfl

theorem cell22_4028362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_4028362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028362 prefixEnd_4028362 := by exact prefixLift 4028362
  have htrace : WordTrace (prefixWord ++ tailWord_4028362) baseStart_4028362 baseEnd_4028362 := by
    simpa [prefixWord, tailWord_4028362, baseEnd_4028362] using wordTrace_append hprefix tailTrace_4028362
  have hstable : (prefixWord ++ tailWord_4028362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028362).length < 2 ^ (prefixWord ++ tailWord_4028362).sum := by decide
  have hdescent : baseEnd_4028362 < baseStart_4028362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028450 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4028450 : Nat := 118140960795 + 4028450 * 2 ^ 59
def prefixEnd_4028450 : Nat := 4983230072969 + 3 ^ 40 * 4028450 * 2
def baseEnd_4028450 : Nat := 1379020761736579269699001

theorem tailTrace_4028450 : CollatzResearch.WordTrace tailWord_4028450 prefixEnd_4028450 1379020761736579269699001 := by
  unfold tailWord_4028450
  simp only [CollatzResearch.WordTrace]
  refine ⟨36732410563905282332568701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97953094837080752886849869 36732410563905282332568701)
  ·
    refine ⟨13774653961464480874713263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36732410563905282332568701 13774653961464480874713263)
    ·
      refine ⟨20661980942196721312069895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13774653961464480874713263 20661980942196721312069895)
      ·
        refine ⟨30992971413295081968104843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20661980942196721312069895 30992971413295081968104843)
        ·
          refine ⟨46489457119942622952157265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30992971413295081968104843 46489457119942622952157265)
          ·
            refine ⟨34867092839956967214117949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46489457119942622952157265 34867092839956967214117949)
            ·
              refine ⟨13075159814983862705294231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34867092839956967214117949 13075159814983862705294231)
              ·
                refine ⟨19612739722475794057941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075159814983862705294231 19612739722475794057941347)
                ·
                  refine ⟨29419109583713691086912021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19612739722475794057941347 29419109583713691086912021)
                  ·
                    refine ⟨1379020761736579269699001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29419109583713691086912021 1379020761736579269699001)
                    ·
                      rfl

theorem cell22_4028450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4028450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028450 prefixEnd_4028450 := by exact prefixLift 4028450
  have htrace : WordTrace (prefixWord ++ tailWord_4028450) baseStart_4028450 baseEnd_4028450 := by
    simpa [prefixWord, tailWord_4028450, baseEnd_4028450] using wordTrace_append hprefix tailTrace_4028450
  have hstable : (prefixWord ++ tailWord_4028450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028450).length < 2 ^ (prefixWord ++ tailWord_4028450).sum := by decide
  have hdescent : baseEnd_4028450 < baseStart_4028450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028604 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_4028604 : Nat := 118140960795 + 4028604 * 2 ^ 59
def prefixEnd_4028604 : Nat := 4983230072969 + 3 ^ 40 * 4028604 * 2
def baseEnd_4028604 : Nat := 1379073479083774201348529

theorem tailTrace_4028604 : CollatzResearch.WordTrace tailWord_4028604 prefixEnd_4028604 1379073479083774201348529 := by
  unfold tailWord_4028604
  simp only [CollatzResearch.WordTrace]
  refine ⟨73467629548531606815690433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97956839398042142420920577 73467629548531606815690433)
  ·
    refine ⟨55100722161398705111767825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73467629548531606815690433 55100722161398705111767825)
    ·
      refine ⟨41325541621049028833825869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55100722161398705111767825 41325541621049028833825869)
      ·
        refine ⟨15497078107893385812684701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41325541621049028833825869 15497078107893385812684701)
        ·
          refine ⟨5811404290460019679756763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15497078107893385812684701 5811404290460019679756763)
          ·
            refine ⟨8717106435690029519635145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811404290460019679756763 8717106435690029519635145)
            ·
              refine ⟨6537829826767522139726359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8717106435690029519635145 6537829826767522139726359)
              ·
                refine ⟨9806744740151283209589539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537829826767522139726359 9806744740151283209589539)
                ·
                  refine ⟨14710117110226924814384309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806744740151283209589539 14710117110226924814384309)
                  ·
                    refine ⟨1379073479083774201348529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14710117110226924814384309 1379073479083774201348529)
                    ·
                      rfl

theorem cell22_4028604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_4028604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028604 prefixEnd_4028604 := by exact prefixLift 4028604
  have htrace : WordTrace (prefixWord ++ tailWord_4028604) baseStart_4028604 baseEnd_4028604 := by
    simpa [prefixWord, tailWord_4028604, baseEnd_4028604] using wordTrace_append hprefix tailTrace_4028604
  have hstable : (prefixWord ++ tailWord_4028604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028604).length < 2 ^ (prefixWord ++ tailWord_4028604).sum := by decide
  have hdescent : baseEnd_4028604 < baseStart_4028604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028754 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_4028754 : Nat := 118140960795 + 4028754 * 2 ^ 59
def prefixEnd_4028754 : Nat := 4983230072969 + 3 ^ 40 * 4028754 * 2
def baseEnd_4028754 : Nat := 1379124827149223810098069

theorem tailTrace_4028754 : CollatzResearch.WordTrace tailWord_4028754 prefixEnd_4028754 1379124827149223810098069 := by
  unfold tailWord_4028754
  simp only [CollatzResearch.WordTrace]
  refine ⟨36735182511629947312335329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97960486697679859499560877 36735182511629947312335329)
  ·
    refine ⟨27551386883722460484251497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36735182511629947312335329 27551386883722460484251497)
    ·
      refine ⟨20663540162791845363188623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27551386883722460484251497 20663540162791845363188623)
      ·
        refine ⟨30995310244187768044782935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20663540162791845363188623 30995310244187768044782935)
        ·
          refine ⟨46492965366281652067174403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30995310244187768044782935 46492965366281652067174403)
          ·
            refine ⟨69739448049422478100761605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46492965366281652067174403 69739448049422478100761605)
            ·
              refine ⟨13076146509266714643892801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69739448049422478100761605 13076146509266714643892801)
              ·
                refine ⟨9807109881950035982919601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13076146509266714643892801 9807109881950035982919601)
                ·
                  refine ⟨7355332411462526987189701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9807109881950035982919601 7355332411462526987189701)
                  ·
                    refine ⟨1379124827149223810098069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355332411462526987189701 1379124827149223810098069)
                    ·
                      rfl

theorem cell22_4028754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_4028754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028754 prefixEnd_4028754 := by exact prefixLift 4028754
  have htrace : WordTrace (prefixWord ++ tailWord_4028754) baseStart_4028754 baseEnd_4028754 := by
    simpa [prefixWord, tailWord_4028754, baseEnd_4028754] using wordTrace_append hprefix tailTrace_4028754
  have hstable : (prefixWord ++ tailWord_4028754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028754).length < 2 ^ (prefixWord ++ tailWord_4028754).sum := by decide
  have hdescent : baseEnd_4028754 < baseStart_4028754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028756 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4028756 : Nat := 118140960795 + 4028756 * 2 ^ 59
def prefixEnd_4028756 : Nat := 4983230072969 + 3 ^ 40 * 4028756 * 2
def baseEnd_4028756 : Nat := 1379125511790096471548063

theorem tailTrace_4028756 : CollatzResearch.WordTrace tailWord_4028756 prefixEnd_4028756 1379125511790096471548063 := by
  unfold tailWord_4028756
  simp only [CollatzResearch.WordTrace]
  refine ⟨73470401496256271795457061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97960535328341695727276081 73470401496256271795457061)
  ·
    refine ⟨13775700280548050961648199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73470401496256271795457061 13775700280548050961648199)
    ·
      refine ⟨20663550420822076442472299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13775700280548050961648199 20663550420822076442472299)
      ·
        refine ⟨30995325631233114663708449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20663550420822076442472299 30995325631233114663708449)
        ·
          refine ⟨23246494223424835997781337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30995325631233114663708449 23246494223424835997781337)
          ·
            refine ⟨17434870667568626998336003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23246494223424835997781337 17434870667568626998336003)
            ·
              refine ⟨26152306001352940497504005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17434870667568626998336003 26152306001352940497504005)
              ·
                refine ⟨4903557375253676343282001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26152306001352940497504005 4903557375253676343282001)
                ·
                  refine ⟨3677668031440257257461501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4903557375253676343282001 3677668031440257257461501)
                  ·
                    refine ⟨1379125511790096471548063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677668031440257257461501 1379125511790096471548063)
                    ·
                      rfl

theorem cell22_4028756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4028756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028756 prefixEnd_4028756 := by exact prefixLift 4028756
  have htrace : WordTrace (prefixWord ++ tailWord_4028756) baseStart_4028756 baseEnd_4028756 := by
    simpa [prefixWord, tailWord_4028756, baseEnd_4028756] using wordTrace_append hprefix tailTrace_4028756
  have hstable : (prefixWord ++ tailWord_4028756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028756).length < 2 ^ (prefixWord ++ tailWord_4028756).sum := by decide
  have hdescent : baseEnd_4028756 < baseStart_4028756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028784 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_4028784 : Nat := 118140960795 + 4028784 * 2 ^ 59
def prefixEnd_4028784 : Nat := 4983230072969 + 3 ^ 40 * 4028784 * 2
def baseEnd_4028784 : Nat := 1379135096762313731847977

theorem tailTrace_4028784 : CollatzResearch.WordTrace tailWord_4028784 prefixEnd_4028784 1379135096762313731847977 := by
  unfold tailWord_4028784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73470912118205552186466703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97961216157607402915288937 73470912118205552186466703)
  ·
    refine ⟨110206368177308328279700055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73470912118205552186466703 110206368177308328279700055)
    ·
      refine ⟨165309552265962492419550083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110206368177308328279700055 165309552265962492419550083)
      ·
        refine ⟨247964328398943738629325125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165309552265962492419550083 247964328398943738629325125)
        ·
          refine ⟨46493311574801950992998461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247964328398943738629325125 46493311574801950992998461)
          ·
            refine ⟨17434991840550731622374423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46493311574801950992998461 17434991840550731622374423)
            ·
              refine ⟨26152487760826097433561635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17434991840550731622374423 26152487760826097433561635)
              ·
                refine ⟨39228731641239146150342453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26152487760826097433561635 39228731641239146150342453)
                ·
                  refine ⟨3677693591366169951594605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39228731641239146150342453 3677693591366169951594605)
                  ·
                    refine ⟨1379135096762313731847977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677693591366169951594605 1379135096762313731847977)
                    ·
                      rfl

theorem cell22_4028784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_4028784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028784 prefixEnd_4028784 := by exact prefixLift 4028784
  have htrace : WordTrace (prefixWord ++ tailWord_4028784) baseStart_4028784 baseEnd_4028784 := by
    simpa [prefixWord, tailWord_4028784, baseEnd_4028784] using wordTrace_append hprefix tailTrace_4028784
  have hstable : (prefixWord ++ tailWord_4028784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028784).length < 2 ^ (prefixWord ++ tailWord_4028784).sum := by decide
  have hdescent : baseEnd_4028784 < baseStart_4028784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028831 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 5]
def baseStart_4028831 : Nat := 118140960795 + 4028831 * 2 ^ 59
def prefixEnd_4028831 : Nat := 4983230072969 + 3 ^ 40 * 4028831 * 2
def baseEnd_4028831 : Nat := 459717061940940425307611

theorem tailTrace_4028831 : CollatzResearch.WordTrace tailWord_4028831 prefixEnd_4028831 459717061940940425307611 := by
  unfold tailWord_4028831
  simp only [CollatzResearch.WordTrace]
  refine ⟨146943538467240831399894347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97962358978160554266596231 146943538467240831399894347)
  ·
    refine ⟨220415307700861247099841521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146943538467240831399894347 220415307700861247099841521)
    ·
      refine ⟨165311480775645935324881141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220415307700861247099841521 165311480775645935324881141)
      ·
        refine ⟨15497951322716806436707607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165311480775645935324881141 15497951322716806436707607)
        ·
          refine ⟨23246926984075209655061411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15497951322716806436707607 23246926984075209655061411)
          ·
            refine ⟨34870390476112814482592117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23246926984075209655061411 34870390476112814482592117)
            ·
              refine ⟨3269099107135576357743011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34870390476112814482592117 3269099107135576357743011)
              ·
                refine ⟨4903648660703364536614517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269099107135576357743011 4903648660703364536614517)
                ·
                  refine ⟨459717061940940425307611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4903648660703364536614517 459717061940940425307611)
                  ·
                    rfl

theorem cell22_4028831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 5].length) (baseStart_4028831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028831 prefixEnd_4028831 := by exact prefixLift 4028831
  have htrace : WordTrace (prefixWord ++ tailWord_4028831) baseStart_4028831 baseEnd_4028831 := by
    simpa [prefixWord, tailWord_4028831, baseEnd_4028831] using wordTrace_append hprefix tailTrace_4028831
  have hstable : (prefixWord ++ tailWord_4028831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028831).length < 2 ^ (prefixWord ++ tailWord_4028831).sum := by decide
  have hdescent : baseEnd_4028831 < baseStart_4028831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028861 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_4028861 : Nat := 118140960795 + 4028861 * 2 ^ 59
def prefixEnd_4028861 : Nat := 4983230072969 + 3 ^ 40 * 4028861 * 2
def baseEnd_4028861 : Nat := 1379161455435911197672741

theorem tailTrace_4028861 : CollatzResearch.WordTrace tailWord_4028861 prefixEnd_4028861 1379161455435911197672741 := by
  unfold tailWord_4028861
  simp only [CollatzResearch.WordTrace]
  refine ⟨146944632657132146523486437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97963088438088097682324291 146944632657132146523486437)
  ·
    refine ⟨27552118623212277473153707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146944632657132146523486437 27552118623212277473153707)
    ·
      refine ⟨41328177934818416209730561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552118623212277473153707 41328177934818416209730561)
      ·
        refine ⟨30996133451113812157297921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41328177934818416209730561 30996133451113812157297921)
        ·
          refine ⟨23247100088335359117973441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30996133451113812157297921 23247100088335359117973441)
          ·
            refine ⟨17435325066251519338480081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23247100088335359117973441 17435325066251519338480081)
            ·
              refine ⟨13076493799688639503860061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17435325066251519338480081 13076493799688639503860061)
              ·
                refine ⟨4903685174883239813947523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13076493799688639503860061 4903685174883239813947523)
                ·
                  refine ⟨7355527762324859720921285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903685174883239813947523 7355527762324859720921285)
                  ·
                    refine ⟨1379161455435911197672741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355527762324859720921285 1379161455435911197672741)
                    ·
                      rfl

theorem cell22_4028861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_4028861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028861 prefixEnd_4028861 := by exact prefixLift 4028861
  have htrace : WordTrace (prefixWord ++ tailWord_4028861) baseStart_4028861 baseEnd_4028861 := by
    simpa [prefixWord, tailWord_4028861, baseEnd_4028861] using wordTrace_append hprefix tailTrace_4028861
  have hstable : (prefixWord ++ tailWord_4028861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028861).length < 2 ^ (prefixWord ++ tailWord_4028861).sum := by decide
  have hdescent : baseEnd_4028861 < baseStart_4028861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028882 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_4028882 : Nat := 118140960795 + 4028882 * 2 ^ 59
def prefixEnd_4028882 : Nat := 4983230072969 + 3 ^ 40 * 4028882 * 2
def baseEnd_4028882 : Nat := 459722881388358047632559

theorem tailTrace_4028882 : CollatzResearch.WordTrace tailWord_4028882 prefixEnd_4028882 459722881388358047632559 := by
  unfold tailWord_4028882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36736349647514016777500225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97963599060037378073333933 36736349647514016777500225)
  ·
    refine ⟨27552262235635512583125169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36736349647514016777500225 27552262235635512583125169)
    ·
      refine ⟨20664196676726634437343877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27552262235635512583125169 20664196676726634437343877)
      ·
        refine ⟨3874536876886243957001977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20664196676726634437343877 3874536876886243957001977)
        ·
          refine ⟨2905902657664682967751483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3874536876886243957001977 2905902657664682967751483)
          ·
            refine ⟨4358853986497024451627225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905902657664682967751483 4358853986497024451627225)
            ·
              refine ⟨3269140489872768338720419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4358853986497024451627225 3269140489872768338720419)
              ·
                refine ⟨4903710734809152508080629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269140489872768338720419 4903710734809152508080629)
                ·
                  refine ⟨459722881388358047632559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4903710734809152508080629 459722881388358047632559)
                  ·
                    rfl

theorem cell22_4028882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_4028882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028882 prefixEnd_4028882 := by exact prefixLift 4028882
  have htrace : WordTrace (prefixWord ++ tailWord_4028882) baseStart_4028882 baseEnd_4028882 := by
    simpa [prefixWord, tailWord_4028882, baseEnd_4028882] using wordTrace_append hprefix tailTrace_4028882
  have hstable : (prefixWord ++ tailWord_4028882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028882).length < 2 ^ (prefixWord ++ tailWord_4028882).sum := by decide
  have hdescent : baseEnd_4028882 < baseStart_4028882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028889 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_4028889 : Nat := 118140960795 + 4028889 * 2 ^ 59
def prefixEnd_4028889 : Nat := 4983230072969 + 3 ^ 40 * 4028889 * 2
def baseEnd_4028889 : Nat := 1379171040408128457972655

theorem tailTrace_4028889 : CollatzResearch.WordTrace tailWord_4028889 prefixEnd_4028889 1379171040408128457972655 := by
  unfold tailWord_4028889
  simp only [CollatzResearch.WordTrace]
  refine ⟨146945653901030707305505721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97963769267353804870337147 146945653901030707305505721)
  ·
    refine ⟨110209240425773030479129291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146945653901030707305505721 110209240425773030479129291)
    ·
      refine ⟨165313860638659545718693937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110209240425773030479129291 165313860638659545718693937)
      ·
        refine ⟨123985395478994659289020453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165313860638659545718693937 123985395478994659289020453)
        ·
          refine ⟨23247261652311498616691335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123985395478994659289020453 23247261652311498616691335)
          ·
            refine ⟨34870892478467247925037003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23247261652311498616691335 34870892478467247925037003)
            ·
              refine ⟨52306338717700871887555505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34870892478467247925037003 52306338717700871887555505)
              ·
                refine ⟨39229754038275653915666629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52306338717700871887555505 39229754038275653915666629)
                ·
                  refine ⟨7355578882176685109187493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39229754038275653915666629 7355578882176685109187493)
                  ·
                    refine ⟨1379171040408128457972655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355578882176685109187493 1379171040408128457972655)
                    ·
                      rfl

theorem cell22_4028889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_4028889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028889 prefixEnd_4028889 := by exact prefixLift 4028889
  have htrace : WordTrace (prefixWord ++ tailWord_4028889) baseStart_4028889 baseEnd_4028889 := by
    simpa [prefixWord, tailWord_4028889, baseEnd_4028889] using wordTrace_append hprefix tailTrace_4028889
  have hstable : (prefixWord ++ tailWord_4028889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028889).length < 2 ^ (prefixWord ++ tailWord_4028889).sum := by decide
  have hdescent : baseEnd_4028889 < baseStart_4028889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028904 : List Nat := [2, 1, 4, 1, 1, 3, 2, 8]
def baseStart_4028904 : Nat := 118140960795 + 4028904 * 2 ^ 59
def prefixEnd_4028904 : Nat := 4983230072969 + 3 ^ 40 * 4028904 * 2
def baseEnd_4028904 : Nat := 153241797246074824316401

theorem tailTrace_4028904 : CollatzResearch.WordTrace tailWord_4028904 prefixEnd_4028904 153241797246074824316401 := by
  unfold tailWord_4028904
  simp only [CollatzResearch.WordTrace]
  refine ⟨73473100497988182433650883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97964133997317576578201177 73473100497988182433650883)
  ·
    refine ⟨110209650746982273650476325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73473100497988182433650883 110209650746982273650476325)
    ·
      refine ⟨20664309515059176309464311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110209650746982273650476325 20664309515059176309464311)
      ·
        refine ⟨30996464272588764464196467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20664309515059176309464311 30996464272588764464196467)
        ·
          refine ⟨46494696408883146696294701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30996464272588764464196467 46494696408883146696294701)
          ·
            refine ⟨17435511153331180011110513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46494696408883146696294701 17435511153331180011110513)
            ·
              refine ⟨13076633364998385008332885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17435511153331180011110513 13076633364998385008332885)
              ·
                refine ⟨153241797246074824316401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13076633364998385008332885 153241797246074824316401)
                ·
                  rfl

theorem cell22_4028904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_4028904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028904 prefixEnd_4028904 := by exact prefixLift 4028904
  have htrace : WordTrace (prefixWord ++ tailWord_4028904) baseStart_4028904 baseEnd_4028904 := by
    simpa [prefixWord, tailWord_4028904, baseEnd_4028904] using wordTrace_append hprefix tailTrace_4028904
  have hstable : (prefixWord ++ tailWord_4028904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028904).length < 2 ^ (prefixWord ++ tailWord_4028904).sum := by decide
  have hdescent : baseEnd_4028904 < baseStart_4028904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028906 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4028906 : Nat := 118140960795 + 4028906 * 2 ^ 59
def prefixEnd_4028906 : Nat := 4983230072969 + 3 ^ 40 * 4028906 * 2
def baseEnd_4028906 : Nat := 1379176859855546080297603

theorem tailTrace_4028906 : CollatzResearch.WordTrace tailWord_4028906 prefixEnd_4028906 1379176859855546080297603 := by
  unfold tailWord_4028906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36736568485492279802218643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97964182627979412805916381 36736568485492279802218643)
  ·
    refine ⟨55104852728238419703327965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36736568485492279802218643 55104852728238419703327965)
    ·
      refine ⟨20664319773089407388747987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55104852728238419703327965 20664319773089407388747987)
      ·
        refine ⟨30996479659634111083121981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20664319773089407388747987 30996479659634111083121981)
        ·
          refine ⟨11623679872362791656170743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30996479659634111083121981 11623679872362791656170743)
          ·
            refine ⟨17435519808544187484256115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623679872362791656170743 17435519808544187484256115)
            ·
              refine ⟨26153279712816281226384173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17435519808544187484256115 26153279712816281226384173)
              ·
                refine ⟨9807479892306105459894065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26153279712816281226384173 9807479892306105459894065)
                ·
                  refine ⟨7355609919229579094920549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9807479892306105459894065 7355609919229579094920549)
                  ·
                    refine ⟨1379176859855546080297603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7355609919229579094920549 1379176859855546080297603)
                    ·
                      rfl

theorem cell22_4028906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4028906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028906 prefixEnd_4028906 := by exact prefixLift 4028906
  have htrace : WordTrace (prefixWord ++ tailWord_4028906) baseStart_4028906 baseEnd_4028906 := by
    simpa [prefixWord, tailWord_4028906, baseEnd_4028906] using wordTrace_append hprefix tailTrace_4028906
  have hstable : (prefixWord ++ tailWord_4028906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028906).length < 2 ^ (prefixWord ++ tailWord_4028906).sum := by decide
  have hdescent : baseEnd_4028906 < baseStart_4028906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028936 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_4028936 : Nat := 118140960795 + 4028936 * 2 ^ 59
def prefixEnd_4028936 : Nat := 4983230072969 + 3 ^ 40 * 4028936 * 2
def baseEnd_4028936 : Nat := 1379187129468636002047511

theorem tailTrace_4028936 : CollatzResearch.WordTrace tailWord_4028936 prefixEnd_4028936 1379187129468636002047511 := by
  unfold tailWord_4028936
  simp only [CollatzResearch.WordTrace]
  refine ⟨73473684065930217166233331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97964912087906956221644441 73473684065930217166233331)
  ·
    refine ⟨110210526098895325749349997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73473684065930217166233331 110210526098895325749349997)
    ·
      refine ⟨41328947287085747156006249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110210526098895325749349997 41328947287085747156006249)
      ·
        refine ⟨30996710465314310367004687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41328947287085747156006249 30996710465314310367004687)
        ·
          refine ⟨46495065697971465550507031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30996710465314310367004687 46495065697971465550507031)
          ·
            refine ⟨69742598546957198325760547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46495065697971465550507031 69742598546957198325760547)
            ·
              refine ⟨104613897820435797488640821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69742598546957198325760547 104613897820435797488640821)
              ·
                refine ⟨9807552920665856014560077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104613897820435797488640821 9807552920665856014560077)
                ·
                  refine ⟨3677832345249696005460029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9807552920665856014560077 3677832345249696005460029)
                  ·
                    refine ⟨1379187129468636002047511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677832345249696005460029 1379187129468636002047511)
                    ·
                      rfl

theorem cell22_4028936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_4028936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028936 prefixEnd_4028936 := by exact prefixLift 4028936
  have htrace : WordTrace (prefixWord ++ tailWord_4028936) baseStart_4028936 baseEnd_4028936 := by
    simpa [prefixWord, tailWord_4028936, baseEnd_4028936] using wordTrace_append hprefix tailTrace_4028936
  have hstable : (prefixWord ++ tailWord_4028936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028936).length < 2 ^ (prefixWord ++ tailWord_4028936).sum := by decide
  have hdescent : baseEnd_4028936 < baseStart_4028936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028970 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4028970 : Nat := 118140960795 + 4028970 * 2 ^ 59
def prefixEnd_4028970 : Nat := 4983230072969 + 3 ^ 40 * 4028970 * 2
def baseEnd_4028970 : Nat := 1379198768363471246697407

theorem tailTrace_4028970 : CollatzResearch.WordTrace tailWord_4028970 prefixEnd_4028970 1379198768363471246697407 := by
  unfold tailWord_4028970
  simp only [CollatzResearch.WordTrace]
  refine ⟨36737152053434314534801091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97965738809158172092802909 36737152053434314534801091)
  ·
    refine ⟨55105728080151471802201637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36737152053434314534801091 55105728080151471802201637)
    ·
      refine ⟨10332324015028400962912807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55105728080151471802201637 10332324015028400962912807)
      ·
        refine ⟨15498486022542601444369211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332324015028400962912807 15498486022542601444369211)
        ·
          refine ⟨23247729033813902166553817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498486022542601444369211 23247729033813902166553817)
          ·
            refine ⟨17435796775360426624915363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23247729033813902166553817 17435796775360426624915363)
            ·
              refine ⟨26153695163040639937373045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17435796775360426624915363 26153695163040639937373045)
              ·
                refine ⟨2451908921535059994128723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26153695163040639937373045 2451908921535059994128723)
                ·
                  refine ⟨3677863382302589991193085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451908921535059994128723 3677863382302589991193085)
                  ·
                    refine ⟨1379198768363471246697407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677863382302589991193085 1379198768363471246697407)
                    ·
                      rfl

theorem cell22_4028970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4028970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4028970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4028970 prefixEnd_4028970 := by exact prefixLift 4028970
  have htrace : WordTrace (prefixWord ++ tailWord_4028970) baseStart_4028970 baseEnd_4028970 := by
    simpa [prefixWord, tailWord_4028970, baseEnd_4028970] using wordTrace_append hprefix tailTrace_4028970
  have hstable : (prefixWord ++ tailWord_4028970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028970).length < 2 ^ (prefixWord ++ tailWord_4028970).sum := by decide
  have hdescent : baseEnd_4028970 < baseStart_4028970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029039 : List Nat := [1, 1, 2, 1, 3, 2, 12]
def baseStart_4029039 : Nat := 118140960795 + 4029039 * 2 ^ 59
def prefixEnd_4029039 : Nat := 4983230072969 + 3 ^ 40 * 4029039 * 2
def baseEnd_4029039 : Nat := 51082310684206595063785

theorem tailTrace_4029039 : CollatzResearch.WordTrace tailWord_4029039 prefixEnd_4029039 51082310684206595063785 := by
  unfold tailWord_4029039
  simp only [CollatzResearch.WordTrace]
  refine ⟨146951124850487282923466171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97967416566991521948977447 146951124850487282923466171)
  ·
    refine ⟨220426687275730924385199257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146951124850487282923466171 220426687275730924385199257)
    ·
      refine ⟨165320015456798193288899443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220426687275730924385199257 165320015456798193288899443)
      ·
        refine ⟨247980023185197289933349165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165320015456798193288899443 247980023185197289933349165)
        ·
          refine ⟨92992508694448983725005937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247980023185197289933349165 92992508694448983725005937)
          ·
            refine ⟨69744381520836737793754453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92992508694448983725005937 69744381520836737793754453)
            ·
              refine ⟨51082310684206595063785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 69744381520836737793754453 51082310684206595063785)
              ·
                rfl

theorem cell22_4029039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 12].length) (baseStart_4029039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029039 prefixEnd_4029039 := by exact prefixLift 4029039
  have htrace : WordTrace (prefixWord ++ tailWord_4029039) baseStart_4029039 baseEnd_4029039 := by
    simpa [prefixWord, tailWord_4029039, baseEnd_4029039] using wordTrace_append hprefix tailTrace_4029039
  have hstable : (prefixWord ++ tailWord_4029039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029039).length < 2 ^ (prefixWord ++ tailWord_4029039).sum := by decide
  have hdescent : baseEnd_4029039 < baseStart_4029039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029045 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 6]
def baseStart_4029045 : Nat := 118140960795 + 4029045 * 2 ^ 59
def prefixEnd_4029045 : Nat := 4983230072969 + 3 ^ 40 * 4029045 * 2
def baseEnd_4029045 : Nat := 459741480798732017024059

theorem tailTrace_4029045 : CollatzResearch.WordTrace tailWord_4029045 prefixEnd_4029045 459741480798732017024059 := by
  unfold tailWord_4029045
  simp only [CollatzResearch.WordTrace]
  refine ⟨146951343688465545948184589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97967562458977030632123059 146951343688465545948184589)
  ·
    refine ⟨55106753883174579730569221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146951343688465545948184589 55106753883174579730569221)
    ·
      refine ⟨10332516353095233699481729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55106753883174579730569221 10332516353095233699481729)
      ·
        refine ⟨7749387264821425274611297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10332516353095233699481729 7749387264821425274611297)
        ·
          refine ⟨5812040448616068955958473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7749387264821425274611297 5812040448616068955958473)
          ·
            refine ⟨4359030336462051716968855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5812040448616068955958473 4359030336462051716968855)
            ·
              refine ⟨6538545504693077575453283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359030336462051716968855 6538545504693077575453283)
              ·
                refine ⟨9807818257039616363179925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538545504693077575453283 9807818257039616363179925)
                ·
                  refine ⟨459741480798732017024059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9807818257039616363179925 459741480798732017024059)
                  ·
                    rfl

theorem cell22_4029045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_4029045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029045 prefixEnd_4029045 := by exact prefixLift 4029045
  have htrace : WordTrace (prefixWord ++ tailWord_4029045) baseStart_4029045 baseEnd_4029045 := by
    simpa [prefixWord, tailWord_4029045, baseEnd_4029045] using wordTrace_append hprefix tailTrace_4029045
  have hstable : (prefixWord ++ tailWord_4029045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029045).length < 2 ^ (prefixWord ++ tailWord_4029045).sum := by decide
  have hdescent : baseEnd_4029045 < baseStart_4029045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029056 : List Nat := [2, 1, 1, 2, 1, 6, 2, 7]
def baseStart_4029056 : Nat := 118140960795 + 4029056 * 2 ^ 59
def prefixEnd_4029056 : Nat := 4983230072969 + 3 ^ 40 * 4029056 * 2
def baseEnd_4029056 : Nat := 153247578657888409894127

theorem tailTrace_4029056 : CollatzResearch.WordTrace tailWord_4029056 prefixEnd_4029056 153247578657888409894127 := by
  unfold tailWord_4029056
  simp only [CollatzResearch.WordTrace]
  refine ⟨73475872445712847413417511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97967829927617129884556681 73475872445712847413417511)
  ·
    refine ⟨110213808668569271120126267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73475872445712847413417511 110213808668569271120126267)
    ·
      refine ⟨165320713002853906680189401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110213808668569271120126267 165320713002853906680189401)
      ·
        refine ⟨123990534752140430010142051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165320713002853906680189401 123990534752140430010142051)
        ·
          refine ⟨185985802128210645015213077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123990534752140430010142051 185985802128210645015213077)
          ·
            refine ⟨8718084474759873985088113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185985802128210645015213077 8718084474759873985088113)
            ·
              refine ⟨6538563356069905488816085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8718084474759873985088113 6538563356069905488816085)
              ·
                refine ⟨153247578657888409894127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6538563356069905488816085 153247578657888409894127)
                ·
                  rfl

theorem cell22_4029056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_4029056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029056 prefixEnd_4029056 := by exact prefixLift 4029056
  have htrace : WordTrace (prefixWord ++ tailWord_4029056) baseStart_4029056 baseEnd_4029056 := by
    simpa [prefixWord, tailWord_4029056, baseEnd_4029056] using wordTrace_append hprefix tailTrace_4029056
  have hstable : (prefixWord ++ tailWord_4029056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029056).length < 2 ^ (prefixWord ++ tailWord_4029056).sum := by decide
  have hdescent : baseEnd_4029056 < baseStart_4029056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029060 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_4029060 : Nat := 118140960795 + 4029060 * 2 ^ 59
def prefixEnd_4029060 : Nat := 4983230072969 + 3 ^ 40 * 4029060 * 2
def baseEnd_4029060 : Nat := 1379229577202741011947131

theorem tailTrace_4029060 : CollatzResearch.WordTrace tailWord_4029060 prefixEnd_4029060 1379229577202741011947131 := by
  unfold tailWord_4029060
  simp only [CollatzResearch.WordTrace]
  refine ⟨73475945391705601754990317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97967927188940802339987089 73475945391705601754990317)
  ·
    refine ⟨27553479521889600658121369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73475945391705601754990317 27553479521889600658121369)
    ·
      refine ⟨20665109641417200493591027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27553479521889600658121369 20665109641417200493591027)
      ·
        refine ⟨30997664462125800740386541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20665109641417200493591027 30997664462125800740386541)
        ·
          refine ⟨11624124173297175277644953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30997664462125800740386541 11624124173297175277644953)
          ·
            refine ⟨8718093129972881458233715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11624124173297175277644953 8718093129972881458233715)
            ·
              refine ⟨13077139694959322187350573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8718093129972881458233715 13077139694959322187350573)
              ·
                refine ⟨4903927385609745820256465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13077139694959322187350573 4903927385609745820256465)
                ·
                  refine ⟨3677945539207309365192349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4903927385609745820256465 3677945539207309365192349)
                  ·
                    refine ⟨1379229577202741011947131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677945539207309365192349 1379229577202741011947131)
                    ·
                      rfl

theorem cell22_4029060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_4029060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029060 prefixEnd_4029060 := by exact prefixLift 4029060
  have htrace : WordTrace (prefixWord ++ tailWord_4029060) baseStart_4029060 baseEnd_4029060 := by
    simpa [prefixWord, tailWord_4029060, baseEnd_4029060] using wordTrace_append hprefix tailTrace_4029060
  have hstable : (prefixWord ++ tailWord_4029060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029060).length < 2 ^ (prefixWord ++ tailWord_4029060).sum := by decide
  have hdescent : baseEnd_4029060 < baseStart_4029060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029118 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4029118 : Nat := 118140960795 + 4029118 * 2 ^ 59
def prefixEnd_4029118 : Nat := 4983230072969 + 3 ^ 40 * 4029118 * 2
def baseEnd_4029118 : Nat := 459749810596016064665651

theorem tailTrace_4029118 : CollatzResearch.WordTrace tailWord_4029118 prefixEnd_4029118 459749810596016064665651 := by
  unfold tailWord_4029118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18369250777150134926949001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97969337478134052943728005 18369250777150134926949001)
  ·
    refine ⟨13776938082862601195211751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18369250777150134926949001 13776938082862601195211751)
    ·
      refine ⟨20665407124293901792817627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13776938082862601195211751 20665407124293901792817627)
      ·
        refine ⟨30998110686440852689226441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20665407124293901792817627 30998110686440852689226441)
        ·
          refine ⟨23248583014830639516919831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30998110686440852689226441 23248583014830639516919831)
          ·
            refine ⟨34872874522245959275379747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23248583014830639516919831 34872874522245959275379747)
            ·
              refine ⟨52309311783368938913069621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34872874522245959275379747 52309311783368938913069621)
              ·
                refine ⟨4903997979690838023100277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52309311783368938913069621 4903997979690838023100277)
                ·
                  refine ⟨459749810596016064665651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4903997979690838023100277 459749810596016064665651)
                  ·
                    rfl

theorem cell22_4029118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4029118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029118 prefixEnd_4029118 := by exact prefixLift 4029118
  have htrace : WordTrace (prefixWord ++ tailWord_4029118) baseStart_4029118 baseEnd_4029118 := by
    simpa [prefixWord, tailWord_4029118, baseEnd_4029118] using wordTrace_append hprefix tailTrace_4029118
  have hstable : (prefixWord ++ tailWord_4029118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029118).length < 2 ^ (prefixWord ++ tailWord_4029118).sum := by decide
  have hdescent : baseEnd_4029118 < baseStart_4029118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029126 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4029126 : Nat := 118140960795 + 4029126 * 2 ^ 59
def prefixEnd_4029126 : Nat := 4983230072969 + 3 ^ 40 * 4029126 * 2
def baseEnd_4029126 : Nat := 1379252170351538839796929

theorem tailTrace_4029126 : CollatzResearch.WordTrace tailWord_4029126 prefixEnd_4029126 1379252170351538839796929 := by
  unfold tailWord_4029126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592321812536628024433851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97969532000781397854588821 4592321812536628024433851)
  ·
    refine ⟨6888482718804942036650777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4592321812536628024433851 6888482718804942036650777)
    ·
      refine ⟨5166362039103706527488083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6888482718804942036650777 5166362039103706527488083)
      ·
        refine ⟨7749543058655559791232125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5166362039103706527488083 7749543058655559791232125)
        ·
          refine ⟨2906078646995834921712047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7749543058655559791232125 2906078646995834921712047)
          ·
            refine ⟨4359117970493752382568071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906078646995834921712047 4359117970493752382568071)
            ·
              refine ⟨6538676955740628573852107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359117970493752382568071 6538676955740628573852107)
              ·
                refine ⟨9808015433610942860778161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538676955740628573852107 9808015433610942860778161)
                ·
                  refine ⟨7356011575208207145583621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808015433610942860778161 7356011575208207145583621)
                  ·
                    refine ⟨1379252170351538839796929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7356011575208207145583621 1379252170351538839796929)
                    ·
                      rfl

theorem cell22_4029126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4029126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029126 prefixEnd_4029126 := by exact prefixLift 4029126
  have htrace : WordTrace (prefixWord ++ tailWord_4029126) baseStart_4029126 baseEnd_4029126 := by
    simpa [prefixWord, tailWord_4029126, baseEnd_4029126] using wordTrace_append hprefix tailTrace_4029126
  have hstable : (prefixWord ++ tailWord_4029126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029126).length < 2 ^ (prefixWord ++ tailWord_4029126).sum := by decide
  have hdescent : baseEnd_4029126 < baseStart_4029126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029146 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_4029146 : Nat := 118140960795 + 4029146 * 2 ^ 59
def prefixEnd_4029146 : Nat := 4983230072969 + 3 ^ 40 * 4029146 * 2
def baseEnd_4029146 : Nat := 459753005586755151432289

theorem tailTrace_4029146 : CollatzResearch.WordTrace tailWord_4029146 prefixEnd_4029146 459753005586755151432289 := by
  unfold tailWord_4029146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36738756865274910049402823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97970018307399760131740861 36738756865274910049402823)
  ·
    refine ⟨55108135297912365074104235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36738756865274910049402823 55108135297912365074104235)
    ·
      refine ⟨82662202946868547611156353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55108135297912365074104235 82662202946868547611156353)
      ·
        refine ⟨61996652210151410708367265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82662202946868547611156353 61996652210151410708367265)
        ·
          refine ⟨46497489157613558031275449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61996652210151410708367265 46497489157613558031275449)
          ·
            refine ⟨34873116868210168523456587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46497489157613558031275449 34873116868210168523456587)
            ·
              refine ⟨52309675302315252785184881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34873116868210168523456587 52309675302315252785184881)
              ·
                refine ⟨39232256476736439588888661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52309675302315252785184881 39232256476736439588888661)
                ·
                  refine ⟨459753005586755151432289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39232256476736439588888661 459753005586755151432289)
                  ·
                    rfl

theorem cell22_4029146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_4029146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029146 prefixEnd_4029146 := by exact prefixLift 4029146
  have htrace : WordTrace (prefixWord ++ tailWord_4029146) baseStart_4029146 baseEnd_4029146 := by
    simpa [prefixWord, tailWord_4029146, baseEnd_4029146] using wordTrace_append hprefix tailTrace_4029146
  have hstable : (prefixWord ++ tailWord_4029146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029146).length < 2 ^ (prefixWord ++ tailWord_4029146).sum := by decide
  have hdescent : baseEnd_4029146 < baseStart_4029146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029161 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_4029161 : Nat := 118140960795 + 4029161 * 2 ^ 59
def prefixEnd_4029161 : Nat := 4983230072969 + 3 ^ 40 * 4029161 * 2
def baseEnd_4029161 : Nat := 1379264151566810415171821

theorem tailTrace_4029161 : CollatzResearch.WordTrace tailWord_4029161 prefixEnd_4029161 1379264151566810415171821 := by
  unfold tailWord_4029161
  simp only [CollatzResearch.WordTrace]
  refine ⟨146955574556045297759407337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97970383037363531839604891 146955574556045297759407337)
  ·
    refine ⟨110216680917033973319555503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146955574556045297759407337 110216680917033973319555503)
    ·
      refine ⟨165325021375550959979333255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110216680917033973319555503 165325021375550959979333255)
      ·
        refine ⟨247987532063326439968999883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165325021375550959979333255 247987532063326439968999883)
        ·
          refine ⟨371981298094989659953499825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247987532063326439968999883 371981298094989659953499825)
          ·
            refine ⟨278985973571242244965124869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371981298094989659953499825 278985973571242244965124869)
            ·
              refine ⟨52309870044607920930960913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278985973571242244965124869 52309870044607920930960913)
              ·
                refine ⟨39232402533455940698220685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52309870044607920930960913 39232402533455940698220685)
                ·
                  refine ⟨14712150950045977761832757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39232402533455940698220685 14712150950045977761832757)
                  ·
                    refine ⟨1379264151566810415171821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14712150950045977761832757 1379264151566810415171821)
                    ·
                      rfl

theorem cell22_4029161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_4029161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029161 prefixEnd_4029161 := by exact prefixLift 4029161
  have htrace : WordTrace (prefixWord ++ tailWord_4029161) baseStart_4029161 baseEnd_4029161 := by
    simpa [prefixWord, tailWord_4029161, baseEnd_4029161] using wordTrace_append hprefix tailTrace_4029161
  have hstable : (prefixWord ++ tailWord_4029161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029161).length < 2 ^ (prefixWord ++ tailWord_4029161).sum := by decide
  have hdescent : baseEnd_4029161 < baseStart_4029161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029176 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_4029176 : Nat := 118140960795 + 4029176 * 2 ^ 59
def prefixEnd_4029176 : Nat := 4983230072969 + 3 ^ 40 * 4029176 * 2
def baseEnd_4029176 : Nat := 1379269286373355376046775

theorem tailTrace_4029176 : CollatzResearch.WordTrace tailWord_4029176 prefixEnd_4029176 1379269286373355376046775 := by
  unfold tailWord_4029176
  simp only [CollatzResearch.WordTrace]
  refine ⟨73478060825495477660601691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97970747767327303547468921 73478060825495477660601691)
  ·
    refine ⟨110217091238243216490902537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73478060825495477660601691 110217091238243216490902537)
    ·
      refine ⟨82662818428682412368176903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110217091238243216490902537 82662818428682412368176903)
      ·
        refine ⟨123994227643023618552265355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82662818428682412368176903 123994227643023618552265355)
        ·
          refine ⟨185991341464535427828398033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123994227643023618552265355 185991341464535427828398033)
          ·
            refine ⟨139493506098401570871298525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185991341464535427828398033 139493506098401570871298525)
            ·
              refine ⟨52310064786900589076736947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139493506098401570871298525 52310064786900589076736947)
              ·
                refine ⟨78465097180350883615105421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52310064786900589076736947 78465097180350883615105421)
                ·
                  refine ⟨29424411442631581355664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78465097180350883615105421 29424411442631581355664533)
                  ·
                    refine ⟨1379269286373355376046775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29424411442631581355664533 1379269286373355376046775)
                    ·
                      rfl

theorem cell22_4029176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_4029176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029176 prefixEnd_4029176 := by exact prefixLift 4029176
  have htrace : WordTrace (prefixWord ++ tailWord_4029176) baseStart_4029176 baseEnd_4029176 := by
    simpa [prefixWord, tailWord_4029176, baseEnd_4029176] using wordTrace_append hprefix tailTrace_4029176
  have hstable : (prefixWord ++ tailWord_4029176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029176).length < 2 ^ (prefixWord ++ tailWord_4029176).sum := by decide
  have hdescent : baseEnd_4029176 < baseStart_4029176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029178 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_4029178 : Nat := 118140960795 + 4029178 * 2 ^ 59
def prefixEnd_4029178 : Nat := 4983230072969 + 3 ^ 40 * 4029178 * 2
def baseEnd_4029178 : Nat := 1379269971014228037496769

theorem tailTrace_4029178 : CollatzResearch.WordTrace tailWord_4029178 prefixEnd_4029178 1379269971014228037496769 := by
  unfold tailWord_4029178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36739048649245927415694047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97970796397989139775184125 36739048649245927415694047)
  ·
    refine ⟨55108572973868891123541071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36739048649245927415694047 55108572973868891123541071)
    ·
      refine ⟨82662859460803336685311607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55108572973868891123541071 82662859460803336685311607)
      ·
        refine ⟨123994289191205005027967411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82662859460803336685311607 123994289191205005027967411)
        ·
          refine ⟨185991433786807507541951117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123994289191205005027967411 185991433786807507541951117)
          ·
            refine ⟨69746787670052815328231669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185991433786807507541951117 69746787670052815328231669)
            ·
              refine ⟨6538761344067451437021719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69746787670052815328231669 6538761344067451437021719)
              ·
                refine ⟨9808142016101177155532579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538761344067451437021719 9808142016101177155532579)
                ·
                  refine ⟨14712213024151765733298869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9808142016101177155532579 14712213024151765733298869)
                  ·
                    refine ⟨1379269971014228037496769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14712213024151765733298869 1379269971014228037496769)
                    ·
                      rfl

theorem cell22_4029178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_4029178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029178 prefixEnd_4029178 := by exact prefixLift 4029178
  have htrace : WordTrace (prefixWord ++ tailWord_4029178) baseStart_4029178 baseEnd_4029178 := by
    simpa [prefixWord, tailWord_4029178, baseEnd_4029178] using wordTrace_append hprefix tailTrace_4029178
  have hstable : (prefixWord ++ tailWord_4029178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029178).length < 2 ^ (prefixWord ++ tailWord_4029178).sum := by decide
  have hdescent : baseEnd_4029178 < baseStart_4029178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029182 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4029182 : Nat := 118140960795 + 4029182 * 2 ^ 59
def prefixEnd_4029182 : Nat := 4983230072969 + 3 ^ 40 * 4029182 * 2
def baseEnd_4029182 : Nat := 1379271340295973360396757

theorem tailTrace_4029182 : CollatzResearch.WordTrace tailWord_4029182 prefixEnd_4029182 1379271340295973360396757 := by
  unfold tailWord_4029182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18369542561121152293240225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97970893659312812230614533 18369542561121152293240225)
  ·
    refine ⟨13777156920840864219930169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18369542561121152293240225 13777156920840864219930169)
    ·
      refine ⟨10332867690630648164947627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13777156920840864219930169 10332867690630648164947627)
      ·
        refine ⟨15499301535945972247421441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332867690630648164947627 15499301535945972247421441)
        ·
          refine ⟨11624476151959479185566081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15499301535945972247421441 11624476151959479185566081)
          ·
            refine ⟨8718357113969609389174561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11624476151959479185566081 8718357113969609389174561)
            ·
              refine ⟨6538767835477207041880921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8718357113969609389174561 6538767835477207041880921)
              ·
                refine ⟨4904075876607905281410691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6538767835477207041880921 4904075876607905281410691)
                ·
                  refine ⟨7356113814911857922116037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904075876607905281410691 7356113814911857922116037)
                  ·
                    refine ⟨1379271340295973360396757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7356113814911857922116037 1379271340295973360396757)
                    ·
                      rfl

theorem cell22_4029182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4029182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029182 prefixEnd_4029182 := by exact prefixLift 4029182
  have htrace : WordTrace (prefixWord ++ tailWord_4029182) baseStart_4029182 baseEnd_4029182 := by
    simpa [prefixWord, tailWord_4029182, baseEnd_4029182] using wordTrace_append hprefix tailTrace_4029182
  have hstable : (prefixWord ++ tailWord_4029182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029182).length < 2 ^ (prefixWord ++ tailWord_4029182).sum := by decide
  have hdescent : baseEnd_4029182 < baseStart_4029182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029274 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_4029274 : Nat := 118140960795 + 4029274 * 2 ^ 59
def prefixEnd_4029274 : Nat := 4983230072969 + 3 ^ 40 * 4029274 * 2
def baseEnd_4029274 : Nat := 1379302833776115787096475

theorem tailTrace_4029274 : CollatzResearch.WordTrace tailWord_4029274 prefixEnd_4029274 1379302833776115787096475 := by
  unfold tailWord_4029274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36739924001158979514567719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97973130669757278705513917 36739924001158979514567719)
  ·
    refine ⟨55109886001738469271851579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36739924001158979514567719 55109886001738469271851579)
    ·
      refine ⟨82664829002607703907777369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55109886001738469271851579 82664829002607703907777369)
      ·
        refine ⟨61998621751955777930833027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82664829002607703907777369 61998621751955777930833027)
        ·
          refine ⟨92997932627933666896249541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61998621751955777930833027 92997932627933666896249541)
          ·
            refine ⟨17437112367737562543046789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92997932627933666896249541 17437112367737562543046789)
            ·
              refine ⟨3269458568950792976821273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17437112367737562543046789 3269458568950792976821273)
              ·
                refine ⟨2452093926713094732615955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269458568950792976821273 2452093926713094732615955)
                ·
                  refine ⟨3678140890069642098923933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452093926713094732615955 3678140890069642098923933)
                  ·
                    refine ⟨1379302833776115787096475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678140890069642098923933 1379302833776115787096475)
                    ·
                      rfl

theorem cell22_4029274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_4029274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029274 prefixEnd_4029274 := by exact prefixLift 4029274
  have htrace : WordTrace (prefixWord ++ tailWord_4029274) baseStart_4029274 baseEnd_4029274 := by
    simpa [prefixWord, tailWord_4029274, baseEnd_4029274] using wordTrace_append hprefix tailTrace_4029274
  have hstable : (prefixWord ++ tailWord_4029274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029274).length < 2 ^ (prefixWord ++ tailWord_4029274).sum := by decide
  have hdescent : baseEnd_4029274 < baseStart_4029274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029298 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_4029298 : Nat := 118140960795 + 4029298 * 2 ^ 59
def prefixEnd_4029298 : Nat := 4983230072969 + 3 ^ 40 * 4029298 * 2
def baseEnd_4029298 : Nat := 459770349822195908165467

theorem tailTrace_4029298 : CollatzResearch.WordTrace tailWord_4029298 prefixEnd_4029298 459770349822195908165467 := by
  unfold tailWord_4029298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740142839137242539286137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97973714237699313438096365 36740142839137242539286137)
  ·
    refine ⟨27555107129352931904464603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36740142839137242539286137 27555107129352931904464603)
    ·
      refine ⟨41332660694029397856696905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27555107129352931904464603 41332660694029397856696905)
      ·
        refine ⟨30999495520522048392522679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41332660694029397856696905 30999495520522048392522679)
        ·
          refine ⟨46499243280783072588784019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30999495520522048392522679 46499243280783072588784019)
          ·
            refine ⟨69748864921174608883176029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46499243280783072588784019 69748864921174608883176029)
            ·
              refine ⟨26155824345440478331191011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69748864921174608883176029 26155824345440478331191011)
              ·
                refine ⟨39233736518160717496786517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26155824345440478331191011 39233736518160717496786517)
                ·
                  refine ⟨459770349822195908165467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39233736518160717496786517 459770349822195908165467)
                  ·
                    rfl

theorem cell22_4029298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_4029298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029298 prefixEnd_4029298 := by exact prefixLift 4029298
  have htrace : WordTrace (prefixWord ++ tailWord_4029298) baseStart_4029298 baseEnd_4029298 := by
    simpa [prefixWord, tailWord_4029298, baseEnd_4029298] using wordTrace_append hprefix tailTrace_4029298
  have hstable : (prefixWord ++ tailWord_4029298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029298).length < 2 ^ (prefixWord ++ tailWord_4029298).sum := by decide
  have hdescent : baseEnd_4029298 < baseStart_4029298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029317 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_4029317 : Nat := 118140960795 + 4029317 * 2 ^ 59
def prefixEnd_4029317 : Nat := 4983230072969 + 3 ^ 40 * 4029317 * 2
def baseEnd_4029317 : Nat := 1379317553554878008271343

theorem tailTrace_4029317 : CollatzResearch.WordTrace tailWord_4029317 prefixEnd_4029317 1379317553554878008271343 := by
  unfold tailWord_4029317
  simp only [CollatzResearch.WordTrace]
  refine ⟨146961264343480136402086205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97974176228986757601390803 146961264343480136402086205)
  ·
    refine ⟨55110474128805051150782327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146961264343480136402086205 55110474128805051150782327)
    ·
      refine ⟨82665711193207576726173491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55110474128805051150782327 82665711193207576726173491)
      ·
        refine ⟨123998566789811365089260237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82665711193207576726173491 123998566789811365089260237)
        ·
          refine ⟨46499462546179261908472589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123998566789811365089260237 46499462546179261908472589)
          ·
            refine ⟨17437298454817223215677221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46499462546179261908472589 17437298454817223215677221)
            ·
              refine ⟨3269493460278229352939479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17437298454817223215677221 3269493460278229352939479)
              ·
                refine ⟨4904240190417344029409219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269493460278229352939479 4904240190417344029409219)
                ·
                  refine ⟨7356360285626016044113829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904240190417344029409219 7356360285626016044113829)
                  ·
                    refine ⟨1379317553554878008271343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7356360285626016044113829 1379317553554878008271343)
                    ·
                      rfl

theorem cell22_4029317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_4029317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029317 prefixEnd_4029317 := by exact prefixLift 4029317
  have htrace : WordTrace (prefixWord ++ tailWord_4029317) baseStart_4029317 baseEnd_4029317 := by
    simpa [prefixWord, tailWord_4029317, baseEnd_4029317] using wordTrace_append hprefix tailTrace_4029317
  have hstable : (prefixWord ++ tailWord_4029317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029317).length < 2 ^ (prefixWord ++ tailWord_4029317).sum := by decide
  have hdescent : baseEnd_4029317 < baseStart_4029317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029332 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 4]
def baseStart_4029332 : Nat := 118140960795 + 4029332 * 2 ^ 59
def prefixEnd_4029332 : Nat := 4983230072969 + 3 ^ 40 * 4029332 * 2
def baseEnd_4029332 : Nat := 459774229453807656382099

theorem tailTrace_4029332 : CollatzResearch.WordTrace tailWord_4029332 prefixEnd_4029332 459774229453807656382099 := by
  unfold tailWord_4029332
  simp only [CollatzResearch.WordTrace]
  refine ⟨73480905719212896981941125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97974540958950529309254833 73480905719212896981941125)
  ·
    refine ⟨13777669822352418184113961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73480905719212896981941125 13777669822352418184113961)
    ·
      refine ⟨10333252366764313638085471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13777669822352418184113961 10333252366764313638085471)
      ·
        refine ⟨15499878550146470457128207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10333252366764313638085471 15499878550146470457128207)
        ·
          refine ⟨23249817825219705685692311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15499878550146470457128207 23249817825219705685692311)
          ·
            refine ⟨34874726737829558528538467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23249817825219705685692311 34874726737829558528538467)
            ·
              refine ⟨52312090106744337792807701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34874726737829558528538467 52312090106744337792807701)
              ·
                refine ⟨2452129223753640834037861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52312090106744337792807701 2452129223753640834037861)
                ·
                  refine ⟨459774229453807656382099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452129223753640834037861 459774229453807656382099)
                  ·
                    rfl

theorem cell22_4029332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_4029332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029332 prefixEnd_4029332 := by exact prefixLift 4029332
  have htrace : WordTrace (prefixWord ++ tailWord_4029332) baseStart_4029332 baseEnd_4029332 := by
    simpa [prefixWord, tailWord_4029332, baseEnd_4029332] using wordTrace_append hprefix tailTrace_4029332
  have hstable : (prefixWord ++ tailWord_4029332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029332).length < 2 ^ (prefixWord ++ tailWord_4029332).sum := by decide
  have hdescent : baseEnd_4029332 < baseStart_4029332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029345 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_4029345 : Nat := 118140960795 + 4029345 * 2 ^ 59
def prefixEnd_4029345 : Nat := 4983230072969 + 3 ^ 40 * 4029345 * 2
def baseEnd_4029345 : Nat := 1379327138527095268571257

theorem tailTrace_4029345 : CollatzResearch.WordTrace tailWord_4029345 prefixEnd_4029345 1379327138527095268571257 := by
  unfold tailWord_4029345
  simp only [CollatzResearch.WordTrace]
  refine ⟨146962285587378697184105489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97974857058252464789403659 146962285587378697184105489)
  ·
    refine ⟨110221714190534022888079117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146962285587378697184105489 110221714190534022888079117)
    ·
      refine ⟨41333142821450258583029669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110221714190534022888079117 41333142821450258583029669)
      ·
        refine ⟨7749964279021923484318063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41333142821450258583029669 7749964279021923484318063)
        ·
          refine ⟨11624946418532885226477095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749964279021923484318063 11624946418532885226477095)
          ·
            refine ⟨17437419627799327839715643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624946418532885226477095 17437419627799327839715643)
            ·
              refine ⟨26156129441698991759573465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437419627799327839715643 26156129441698991759573465)
              ·
                refine ⟨19617097081274243819680099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26156129441698991759573465 19617097081274243819680099)
                ·
                  refine ⟨29425645621911365729520149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19617097081274243819680099 29425645621911365729520149)
                  ·
                    refine ⟨1379327138527095268571257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29425645621911365729520149 1379327138527095268571257)
                    ·
                      rfl

theorem cell22_4029345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_4029345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029345 prefixEnd_4029345 := by exact prefixLift 4029345
  have htrace : WordTrace (prefixWord ++ tailWord_4029345) baseStart_4029345 baseEnd_4029345 := by
    simpa [prefixWord, tailWord_4029345, baseEnd_4029345] using wordTrace_append hprefix tailTrace_4029345
  have hstable : (prefixWord ++ tailWord_4029345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029345).length < 2 ^ (prefixWord ++ tailWord_4029345).sum := by decide
  have hdescent : baseEnd_4029345 < baseStart_4029345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029364 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4029364 : Nat := 118140960795 + 4029364 * 2 ^ 59
def prefixEnd_4029364 : Nat := 4983230072969 + 3 ^ 40 * 4029364 * 2
def baseEnd_4029364 : Nat := 1379333642615385552346199

theorem tailTrace_4029364 : CollatzResearch.WordTrace tailWord_4029364 prefixEnd_4029364 1379333642615385552346199 := by
  unfold tailWord_4029364
  simp only [CollatzResearch.WordTrace]
  refine ⟨73481489287154931714523573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97975319049539908952698097 73481489287154931714523573)
  ·
    refine ⟨6888889620670774848236585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73481489287154931714523573 6888889620670774848236585)
    ·
      refine ⟨5166667215503081136177439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6888889620670774848236585 5166667215503081136177439)
      ·
        refine ⟨7750000823254621704266159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5166667215503081136177439 7750000823254621704266159)
        ·
          refine ⟨11625001234881932556399239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7750000823254621704266159 11625001234881932556399239)
          ·
            refine ⟨17437501852322898834598859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11625001234881932556399239 17437501852322898834598859)
            ·
              refine ⟨26156252778484348251898289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437501852322898834598859 26156252778484348251898289)
              ·
                refine ⟨19617189583863261188923717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26156252778484348251898289 19617189583863261188923717)
                ·
                  refine ⟨3678223046974361472923197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19617189583863261188923717 3678223046974361472923197)
                  ·
                    refine ⟨1379333642615385552346199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678223046974361472923197 1379333642615385552346199)
                    ·
                      rfl

theorem cell22_4029364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4029364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029364 prefixEnd_4029364 := by exact prefixLift 4029364
  have htrace : WordTrace (prefixWord ++ tailWord_4029364) baseStart_4029364 baseEnd_4029364 := by
    simpa [prefixWord, tailWord_4029364, baseEnd_4029364] using wordTrace_append hprefix tailTrace_4029364
  have hstable : (prefixWord ++ tailWord_4029364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029364).length < 2 ^ (prefixWord ++ tailWord_4029364).sum := by decide
  have hdescent : baseEnd_4029364 < baseStart_4029364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029398 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4029398 : Nat := 118140960795 + 4029398 * 2 ^ 59
def prefixEnd_4029398 : Nat := 4983230072969 + 3 ^ 40 * 4029398 * 2
def baseEnd_4029398 : Nat := 1379345281510220796996095

theorem tailTrace_4029398 : CollatzResearch.WordTrace tailWord_4029398 prefixEnd_4029398 1379345281510220796996095 := by
  unfold tailWord_4029398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9185263666011667952236553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97976145770791124823856565 9185263666011667952236553)
  ·
    refine ⟨6888947749508750964177415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9185263666011667952236553 6888947749508750964177415)
    ·
      refine ⟨10333421624263126446266123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888947749508750964177415 10333421624263126446266123)
      ·
        refine ⟨15500132436394689669399185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10333421624263126446266123 15500132436394689669399185)
        ·
          refine ⟨11625099327296017252049389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15500132436394689669399185 11625099327296017252049389)
          ·
            refine ⟨4359412247736006469518521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11625099327296017252049389 4359412247736006469518521)
            ·
              refine ⟨3269559185802004852138891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4359412247736006469518521 3269559185802004852138891)
              ·
                refine ⟨4904338778703007278208337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269559185802004852138891 4904338778703007278208337)
                ·
                  refine ⟨3678254084027255458656253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904338778703007278208337 3678254084027255458656253)
                  ·
                    refine ⟨1379345281510220796996095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678254084027255458656253 1379345281510220796996095)
                    ·
                      rfl

theorem cell22_4029398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4029398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029398 prefixEnd_4029398 := by exact prefixLift 4029398
  have htrace : WordTrace (prefixWord ++ tailWord_4029398) baseStart_4029398 baseEnd_4029398 := by
    simpa [prefixWord, tailWord_4029398, baseEnd_4029398] using wordTrace_append hprefix tailTrace_4029398
  have hstable : (prefixWord ++ tailWord_4029398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029398).length < 2 ^ (prefixWord ++ tailWord_4029398).sum := by decide
  have hdescent : baseEnd_4029398 < baseStart_4029398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029465 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_4029465 : Nat := 118140960795 + 4029465 * 2 ^ 59
def prefixEnd_4029465 : Nat := 4983230072969 + 3 ^ 40 * 4029465 * 2
def baseEnd_4029465 : Nat := 1379368216979454955570889

theorem tailTrace_4029465 : CollatzResearch.WordTrace tailWord_4029465 prefixEnd_4029465 1379368216979454955570889 := by
  unfold tailWord_4029465
  simp only [CollatzResearch.WordTrace]
  refine ⟨146966662346943957678473849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97977774897962638452315899 146966662346943957678473849)
  ·
    refine ⟨110224996760207968258855387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146966662346943957678473849 110224996760207968258855387)
    ·
      refine ⟨165337495140311952388283081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110224996760207968258855387 165337495140311952388283081)
      ·
        refine ⟨124003121355233964291212311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165337495140311952388283081 124003121355233964291212311)
        ·
          refine ⟨186004682032850946436818467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124003121355233964291212311 186004682032850946436818467)
          ·
            refine ⟨279007023049276419655227701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186004682032850946436818467 279007023049276419655227701)
            ·
              refine ⟨26156908410869664342677597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279007023049276419655227701 26156908410869664342677597)
              ·
                refine ⟨9808840654076124128504099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26156908410869664342677597 9808840654076124128504099)
                ·
                  refine ⟨14713260981114186192756149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9808840654076124128504099 14713260981114186192756149)
                  ·
                    refine ⟨1379368216979454955570889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14713260981114186192756149 1379368216979454955570889)
                    ·
                      rfl

theorem cell22_4029465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_4029465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029465 prefixEnd_4029465 := by exact prefixLift 4029465
  have htrace : WordTrace (prefixWord ++ tailWord_4029465) baseStart_4029465 baseEnd_4029465 := by
    simpa [prefixWord, tailWord_4029465, baseEnd_4029465] using wordTrace_append hprefix tailTrace_4029465
  have hstable : (prefixWord ++ tailWord_4029465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029465).length < 2 ^ (prefixWord ++ tailWord_4029465).sum := by decide
  have hdescent : baseEnd_4029465 < baseStart_4029465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029561 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_4029561 : Nat := 118140960795 + 4029561 * 2 ^ 59
def prefixEnd_4029561 : Nat := 4983230072969 + 3 ^ 40 * 4029561 * 2
def baseEnd_4029561 : Nat := 1379401079741342705170595

theorem tailTrace_4029561 : CollatzResearch.WordTrace tailWord_4029561 prefixEnd_4029561 1379401079741342705170595 := by
  unfold tailWord_4029561
  simp only [CollatzResearch.WordTrace]
  refine ⟨146970163754596166073968537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97980109169730777382645691 146970163754596166073968537)
  ·
    refine ⟨110227622815947124555476403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146970163754596166073968537 110227622815947124555476403)
    ·
      refine ⟨165341434223920686833214605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110227622815947124555476403 165341434223920686833214605)
      ·
        refine ⟨62003037833970257562455477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165341434223920686833214605 62003037833970257562455477)
        ·
          refine ⟨5812784796934711646480201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62003037833970257562455477 5812784796934711646480201)
          ·
            refine ⟨4359588597701033734860151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5812784796934711646480201 4359588597701033734860151)
            ·
              refine ⟨6539382896551550602290227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359588597701033734860151 6539382896551550602290227)
              ·
                refine ⟨9809074344827325903435341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539382896551550602290227 9809074344827325903435341)
                ·
                  refine ⟨3678402879310247213788253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9809074344827325903435341 3678402879310247213788253)
                  ·
                    refine ⟨1379401079741342705170595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678402879310247213788253 1379401079741342705170595)
                    ·
                      rfl

theorem cell22_4029561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_4029561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029561 prefixEnd_4029561 := by exact prefixLift 4029561
  have htrace : WordTrace (prefixWord ++ tailWord_4029561) baseStart_4029561 baseEnd_4029561 := by
    simpa [prefixWord, tailWord_4029561, baseEnd_4029561] using wordTrace_append hprefix tailTrace_4029561
  have hstable : (prefixWord ++ tailWord_4029561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029561).length < 2 ^ (prefixWord ++ tailWord_4029561).sum := by decide
  have hdescent : baseEnd_4029561 < baseStart_4029561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029698 : List Nat := [3, 4, 1, 1, 3, 2, 2, 6]
def baseStart_4029698 : Nat := 118140960795 + 4029698 * 2 ^ 59
def prefixEnd_4029698 : Nat := 4983230072969 + 3 ^ 40 * 4029698 * 2
def baseEnd_4029698 : Nat := 153271997515680001610575

theorem tailTrace_4029698 : CollatzResearch.WordTrace tailWord_4029698 prefixEnd_4029698 153271997515680001610575 := by
  unfold tailWord_4029698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36743790138774959617926437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97983440370066558981137165 36743790138774959617926437)
  ·
    refine ⟨6889460651020304928361207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36743790138774959617926437 6889460651020304928361207)
    ·
      refine ⟨10334190976530457392541811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6889460651020304928361207 10334190976530457392541811)
      ·
        refine ⟨15501286464795686088812717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10334190976530457392541811 15501286464795686088812717)
        ·
          refine ⟨5812982424298382283304769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15501286464795686088812717 5812982424298382283304769)
          ·
            refine ⟨4359736818223786712478577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5812982424298382283304769 4359736818223786712478577)
            ·
              refine ⟨3269802613667840034358933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4359736818223786712478577 3269802613667840034358933)
              ·
                refine ⟨153271997515680001610575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3269802613667840034358933 153271997515680001610575)
                ·
                  rfl

theorem cell22_4029698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_4029698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029698 prefixEnd_4029698 := by exact prefixLift 4029698
  have htrace : WordTrace (prefixWord ++ tailWord_4029698) baseStart_4029698 baseEnd_4029698 := by
    simpa [prefixWord, tailWord_4029698, baseEnd_4029698] using wordTrace_append hprefix tailTrace_4029698
  have hstable : (prefixWord ++ tailWord_4029698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029698).length < 2 ^ (prefixWord ++ tailWord_4029698).sum := by decide
  have hdescent : baseEnd_4029698 < baseStart_4029698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
