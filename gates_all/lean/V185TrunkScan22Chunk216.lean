import V185TrunkScan22Chunk215

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1926263 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1926263 : Nat := 118140960795 + 1926263 * 2 ^ 59
def prefixEnd_1926263 : Nat := 4983230072969 + 3 ^ 40 * 1926263 * 2
def baseEnd_1926263 : Nat := 659399190647801480569189

theorem tailTrace_1926263 : CollatzResearch.WordTrace tailWord_1926263 prefixEnd_1926263 659399190647801480569189 := by
  unfold tailWord_1926263
  simp only [CollatzResearch.WordTrace]
  refine ⟨70256583420485605374111443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46837722280323736916074295 70256583420485605374111443)
  ·
    refine ⟨105384875130728408061167165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70256583420485605374111443 105384875130728408061167165)
    ·
      refine ⟨39519328174023153022937687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105384875130728408061167165 39519328174023153022937687)
      ·
        refine ⟨59278992261034729534406531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39519328174023153022937687 59278992261034729534406531)
        ·
          refine ⟨88918488391552094301609797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59278992261034729534406531 88918488391552094301609797)
          ·
            refine ⟨16672216573416017681551837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88918488391552094301609797 16672216573416017681551837)
            ·
              refine ⟨6252081215031006630581939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16672216573416017681551837 6252081215031006630581939)
              ·
                refine ⟨9378121822546509945872909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252081215031006630581939 9378121822546509945872909)
                ·
                  refine ⟨3516795683454941229702341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9378121822546509945872909 3516795683454941229702341)
                  ·
                    refine ⟨659399190647801480569189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3516795683454941229702341 659399190647801480569189)
                    ·
                      rfl

theorem cell22_1926263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1926263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926263 prefixEnd_1926263 := by exact prefixLift 1926263
  have htrace : WordTrace (prefixWord ++ tailWord_1926263) baseStart_1926263 baseEnd_1926263 := by
    simpa [prefixWord, tailWord_1926263, baseEnd_1926263] using wordTrace_append hprefix tailTrace_1926263
  have hstable : (prefixWord ++ tailWord_1926263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926263).length < 2 ^ (prefixWord ++ tailWord_1926263).sum := by decide
  have hdescent : baseEnd_1926263 < baseStart_1926263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926340 : List Nat := [2, 3, 3, 1, 3, 1, 9]
def baseStart_1926340 : Nat := 118140960795 + 1926340 * 2 ^ 59
def prefixEnd_1926340 : Nat := 4983230072969 + 3 ^ 40 * 1926340 * 2
def baseEnd_1926340 : Nat := 24423168493385146162739

theorem tailTrace_1926340 : CollatzResearch.WordTrace tailWord_1926340 prefixEnd_1926340 24423168493385146162739 := by
  unfold tailWord_1926340
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129695920603323762332237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46839594560804431683109649 35129695920603323762332237)
  ·
    refine ⟨13173635970226246410874589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35129695920603323762332237 13173635970226246410874589)
    ·
      refine ⟨4940113488834842404077971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13173635970226246410874589 4940113488834842404077971)
      ·
        refine ⟨7410170233252263606116957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940113488834842404077971 7410170233252263606116957)
        ·
          refine ⟨2778813837469598852293859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7410170233252263606116957 2778813837469598852293859)
          ·
            refine ⟨4168220756204398278440789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778813837469598852293859 4168220756204398278440789)
            ·
              refine ⟨24423168493385146162739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4168220756204398278440789 24423168493385146162739)
              ·
                rfl

theorem cell22_1926340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 9].length) (baseStart_1926340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926340 prefixEnd_1926340 := by exact prefixLift 1926340
  have htrace : WordTrace (prefixWord ++ tailWord_1926340) baseStart_1926340 baseEnd_1926340 := by
    simpa [prefixWord, tailWord_1926340, baseEnd_1926340] using wordTrace_append hprefix tailTrace_1926340
  have hstable : (prefixWord ++ tailWord_1926340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926340).length < 2 ^ (prefixWord ++ tailWord_1926340).sum := by decide
  have hdescent : baseEnd_1926340 < baseStart_1926340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926432 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_1926432 : Nat := 118140960795 + 1926432 * 2 ^ 59
def prefixEnd_1926432 : Nat := 4983230072969 + 3 ^ 40 * 1926432 * 2
def baseEnd_1926432 : Nat := 659457042801541373093671

theorem tailTrace_1926432 : CollatzResearch.WordTrace tailWord_1926432 prefixEnd_1926432 659457042801541373093671 := by
  unfold tailWord_1926432
  simp only [CollatzResearch.WordTrace]
  refine ⟨35131373678436673618506775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46841831571248898158009033 35131373678436673618506775)
  ·
    refine ⟨52697060517655010427760163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35131373678436673618506775 52697060517655010427760163)
    ·
      refine ⟨79045590776482515641640245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52697060517655010427760163 79045590776482515641640245)
      ·
        refine ⟨7410524135295235841403773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79045590776482515641640245 7410524135295235841403773)
        ·
          refine ⟨2778946550735713440526415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7410524135295235841403773 2778946550735713440526415)
          ·
            refine ⟨4168419826103570160789623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778946550735713440526415 4168419826103570160789623)
            ·
              refine ⟨6252629739155355241184435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168419826103570160789623 6252629739155355241184435)
              ·
                refine ⟨9378944608733032861776653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252629739155355241184435 9378944608733032861776653)
                ·
                  refine ⟨3517104228274887323166245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9378944608733032861776653 3517104228274887323166245)
                  ·
                    refine ⟨659457042801541373093671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517104228274887323166245 659457042801541373093671)
                    ·
                      rfl

theorem cell22_1926432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_1926432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926432 prefixEnd_1926432 := by exact prefixLift 1926432
  have htrace : WordTrace (prefixWord ++ tailWord_1926432) baseStart_1926432 baseEnd_1926432 := by
    simpa [prefixWord, tailWord_1926432, baseEnd_1926432] using wordTrace_append hprefix tailTrace_1926432
  have hstable : (prefixWord ++ tailWord_1926432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926432).length < 2 ^ (prefixWord ++ tailWord_1926432).sum := by decide
  have hdescent : baseEnd_1926432 < baseStart_1926432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926449 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 1, 4]
def baseStart_1926449 : Nat := 118140960795 + 1926449 * 2 ^ 59
def prefixEnd_1926449 : Nat := 4983230072969 + 3 ^ 40 * 1926449 * 2
def baseEnd_1926449 : Nat := 659462862248958995418619

theorem tailTrace_1926449 : CollatzResearch.WordTrace tailWord_1926449 prefixEnd_1926449 659462862248958995418619 := by
  unfold tailWord_1926449
  simp only [CollatzResearch.WordTrace]
  refine ⟨70263367397811759140382401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46842244931874506093588267 70263367397811759140382401)
  ·
    refine ⟨52697525548358819355286801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70263367397811759140382401 52697525548358819355286801)
    ·
      refine ⟨39523144161269114516465101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52697525548358819355286801 39523144161269114516465101)
      ·
        refine ⟨14821179060475917943674413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39523144161269114516465101 14821179060475917943674413)
        ·
          refine ⟨5557942147678469228877905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14821179060475917943674413 5557942147678469228877905)
          ·
            refine ⟨4168456610758851921658429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557942147678469228877905 4168456610758851921658429)
            ·
              refine ⟨1563171229034569470621911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4168456610758851921658429 1563171229034569470621911)
              ·
                refine ⟨2344756843551854205932867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563171229034569470621911 2344756843551854205932867)
                ·
                  refine ⟨3517135265327781308899301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344756843551854205932867 3517135265327781308899301)
                  ·
                    refine ⟨659462862248958995418619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517135265327781308899301 659462862248958995418619)
                    ·
                      rfl

theorem cell22_1926449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_1926449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926449 prefixEnd_1926449 := by exact prefixLift 1926449
  have htrace : WordTrace (prefixWord ++ tailWord_1926449) baseStart_1926449 baseEnd_1926449 := by
    simpa [prefixWord, tailWord_1926449, baseEnd_1926449] using wordTrace_append hprefix tailTrace_1926449
  have hstable : (prefixWord ++ tailWord_1926449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926449).length < 2 ^ (prefixWord ++ tailWord_1926449).sum := by decide
  have hdescent : baseEnd_1926449 < baseStart_1926449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926524 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_1926524 : Nat := 118140960795 + 1926524 * 2 ^ 59
def prefixEnd_1926524 : Nat := 4983230072969 + 3 ^ 40 * 1926524 * 2
def baseEnd_1926524 : Nat := 659488536281683799793389

theorem tailTrace_1926524 : CollatzResearch.WordTrace tailWord_1926524 prefixEnd_1926524 659488536281683799793389 := by
  unfold tailWord_1926524
  simp only [CollatzResearch.WordTrace]
  refine ⟨35133051436270023474681313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46844068581693364632908417 35133051436270023474681313)
  ·
    refine ⟨26349788577202517606010985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35133051436270023474681313 26349788577202517606010985)
    ·
      refine ⟨19762341432901888204508239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26349788577202517606010985 19762341432901888204508239)
      ·
        refine ⟨29643512149352832306762359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19762341432901888204508239 29643512149352832306762359)
        ·
          refine ⟨44465268224029248460143539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29643512149352832306762359 44465268224029248460143539)
          ·
            refine ⟨66697902336043872690215309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44465268224029248460143539 66697902336043872690215309)
            ·
              refine ⟨25011713376016452258830741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66697902336043872690215309 25011713376016452258830741)
              ·
                refine ⟨1172424064500771199632691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25011713376016452258830741 1172424064500771199632691)
                ·
                  refine ⟨1758636096751156799449037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172424064500771199632691 1758636096751156799449037)
                  ·
                    refine ⟨659488536281683799793389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1758636096751156799449037 659488536281683799793389)
                    ·
                      rfl

theorem cell22_1926524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_1926524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926524 prefixEnd_1926524 := by exact prefixLift 1926524
  have htrace : WordTrace (prefixWord ++ tailWord_1926524) baseStart_1926524 baseEnd_1926524 := by
    simpa [prefixWord, tailWord_1926524, baseEnd_1926524] using wordTrace_append hprefix tailTrace_1926524
  have hstable : (prefixWord ++ tailWord_1926524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926524).length < 2 ^ (prefixWord ++ tailWord_1926524).sum := by decide
  have hdescent : baseEnd_1926524 < baseStart_1926524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926588 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 5]
def baseStart_1926588 : Nat := 118140960795 + 1926588 * 2 ^ 59
def prefixEnd_1926588 : Nat := 4983230072969 + 3 ^ 40 * 1926588 * 2
def baseEnd_1926588 : Nat := 219836814929869655397731

theorem tailTrace_1926588 : CollatzResearch.WordTrace tailWord_1926588 prefixEnd_1926588 219836814929869655397731 := by
  unfold tailWord_1926588
  simp only [CollatzResearch.WordTrace]
  refine ⟨35134218572154092939846209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46845624762872123919794945 35134218572154092939846209)
  ·
    refine ⟨26350663929115569704884657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35134218572154092939846209 26350663929115569704884657)
    ·
      refine ⟨19762997946836677278663493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26350663929115569704884657 19762997946836677278663493)
      ·
        refine ⟨3705562115031876989749405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19762997946836677278663493 3705562115031876989749405)
        ·
          refine ⟨1389585793136953871156027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3705562115031876989749405 1389585793136953871156027)
          ·
            refine ⟨2084378689705430806734041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389585793136953871156027 2084378689705430806734041)
            ·
              refine ⟨1563284017279073105050531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2084378689705430806734041 1563284017279073105050531)
              ·
                refine ⟨2344926025918609657575797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563284017279073105050531 2344926025918609657575797)
                ·
                  refine ⟨219836814929869655397731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2344926025918609657575797 219836814929869655397731)
                  ·
                    rfl

theorem cell22_1926588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_1926588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926588 prefixEnd_1926588 := by exact prefixLift 1926588
  have htrace : WordTrace (prefixWord ++ tailWord_1926588) baseStart_1926588 baseEnd_1926588 := by
    simpa [prefixWord, tailWord_1926588, baseEnd_1926588] using wordTrace_append hprefix tailTrace_1926588
  have hstable : (prefixWord ++ tailWord_1926588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926588).length < 2 ^ (prefixWord ++ tailWord_1926588).sum := by decide
  have hdescent : baseEnd_1926588 < baseStart_1926588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926595 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_1926595 : Nat := 118140960795 + 1926595 * 2 ^ 59
def prefixEnd_1926595 : Nat := 4983230072969 + 3 ^ 40 * 1926595 * 2
def baseEnd_1926595 : Nat := 659512841032663281268171

theorem tailTrace_1926595 : CollatzResearch.WordTrace tailWord_1926595 prefixEnd_1926595 659512841032663281268171 := by
  unfold tailWord_1926595
  simp only [CollatzResearch.WordTrace]
  refine ⟨70268692455282826075197239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46845794970188550716798159 70268692455282826075197239)
  ·
    refine ⟨105403038682924239112795859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70268692455282826075197239 105403038682924239112795859)
    ·
      refine ⟨158104558024386358669193789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105403038682924239112795859 158104558024386358669193789)
      ·
        refine ⟨59289209259144884500947671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158104558024386358669193789 59289209259144884500947671)
        ·
          refine ⟨88933813888717326751421507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59289209259144884500947671 88933813888717326751421507)
          ·
            refine ⟨133400720833075990127132261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88933813888717326751421507 133400720833075990127132261)
            ·
              refine ⟨25012635156201748148837299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133400720833075990127132261 25012635156201748148837299)
              ·
                refine ⟨37518952734302622223255949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25012635156201748148837299 37518952734302622223255949)
                ·
                  refine ⟨14069607275363483333720981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37518952734302622223255949 14069607275363483333720981)
                  ·
                    refine ⟨659512841032663281268171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14069607275363483333720981 659512841032663281268171)
                    ·
                      rfl

theorem cell22_1926595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_1926595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926595 prefixEnd_1926595 := by exact prefixLift 1926595
  have htrace : WordTrace (prefixWord ++ tailWord_1926595) baseStart_1926595 baseEnd_1926595 := by
    simpa [prefixWord, tailWord_1926595, baseEnd_1926595] using wordTrace_append hprefix tailTrace_1926595
  have hstable : (prefixWord ++ tailWord_1926595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926595).length < 2 ^ (prefixWord ++ tailWord_1926595).sum := by decide
  have hdescent : baseEnd_1926595 < baseStart_1926595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926614 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1926614 : Nat := 118140960795 + 1926614 * 2 ^ 59
def prefixEnd_1926614 : Nat := 4983230072969 + 3 ^ 40 * 1926614 * 2
def baseEnd_1926614 : Nat := 659519345120953565043113

theorem tailTrace_1926614 : CollatzResearch.WordTrace tailWord_1926614 prefixEnd_1926614 659519345120953565043113 := by
  unfold tailWord_1926614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391836590138374520008681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46846256961475994880092597 4391836590138374520008681)
  ·
    refine ⟨3293877442603780890006511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391836590138374520008681 3293877442603780890006511)
    ·
      refine ⟨4940816163905671335009767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293877442603780890006511 4940816163905671335009767)
      ·
        refine ⟨7411224245858507002514651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940816163905671335009767 7411224245858507002514651)
        ·
          refine ⟨11116836368787760503771977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411224245858507002514651 11116836368787760503771977)
          ·
            refine ⟨8337627276590820377828983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11116836368787760503771977 8337627276590820377828983)
            ·
              refine ⟨12506440914886230566743475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337627276590820377828983 12506440914886230566743475)
              ·
                refine ⟨18759661372329345850115213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506440914886230566743475 18759661372329345850115213)
                ·
                  refine ⟨7034873014623504693793205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18759661372329345850115213 7034873014623504693793205)
                  ·
                    refine ⟨659519345120953565043113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7034873014623504693793205 659519345120953565043113)
                    ·
                      rfl

theorem cell22_1926614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1926614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926614 prefixEnd_1926614 := by exact prefixLift 1926614
  have htrace : WordTrace (prefixWord ++ tailWord_1926614) baseStart_1926614 baseEnd_1926614 := by
    simpa [prefixWord, tailWord_1926614, baseEnd_1926614] using wordTrace_append hprefix tailTrace_1926614
  have hstable : (prefixWord ++ tailWord_1926614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926614).length < 2 ^ (prefixWord ++ tailWord_1926614).sum := by decide
  have hdescent : baseEnd_1926614 < baseStart_1926614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926629 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1926629 : Nat := 118140960795 + 1926629 * 2 ^ 59
def prefixEnd_1926629 : Nat := 4983230072969 + 3 ^ 40 * 1926629 * 2
def baseEnd_1926629 : Nat := 659524479927498525918067

theorem tailTrace_1926629 : CollatzResearch.WordTrace tailWord_1926629 prefixEnd_1926629 659524479927498525918067 := by
  unfold tailWord_1926629
  simp only [CollatzResearch.WordTrace]
  refine ⟨70269932537159649881934941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46846621691439766587956627 70269932537159649881934941)
  ·
    refine ⟨26351224701434868705725603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70269932537159649881934941 26351224701434868705725603)
    ·
      refine ⟨39526837052152303058588405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26351224701434868705725603 39526837052152303058588405)
      ·
        refine ⟨3705640973639278411742663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39526837052152303058588405 3705640973639278411742663)
        ·
          refine ⟨5558461460458917617613995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705640973639278411742663 5558461460458917617613995)
          ·
            refine ⟨8337692190688376426420993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558461460458917617613995 8337692190688376426420993)
            ·
              refine ⟨6253269143016282319815745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337692190688376426420993 6253269143016282319815745)
              ·
                refine ⟨4689951857262211739861809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253269143016282319815745 4689951857262211739861809)
                ·
                  refine ⟨3517463892946658804896357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4689951857262211739861809 3517463892946658804896357)
                  ·
                    refine ⟨659524479927498525918067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517463892946658804896357 659524479927498525918067)
                    ·
                      rfl

theorem cell22_1926629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1926629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926629 prefixEnd_1926629 := by exact prefixLift 1926629
  have htrace : WordTrace (prefixWord ++ tailWord_1926629) baseStart_1926629 baseEnd_1926629 := by
    simpa [prefixWord, tailWord_1926629, baseEnd_1926629] using wordTrace_append hprefix tailTrace_1926629
  have hstable : (prefixWord ++ tailWord_1926629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926629).length < 2 ^ (prefixWord ++ tailWord_1926629).sum := by decide
  have hdescent : baseEnd_1926629 < baseStart_1926629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926631 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1926631 : Nat := 118140960795 + 1926631 * 2 ^ 59
def prefixEnd_1926631 : Nat := 4983230072969 + 3 ^ 40 * 1926631 * 2
def baseEnd_1926631 : Nat := 659525164568371187368061

theorem tailTrace_1926631 : CollatzResearch.WordTrace tailWord_1926631 prefixEnd_1926631 659525164568371187368061 := by
  unfold tailWord_1926631
  simp only [CollatzResearch.WordTrace]
  refine ⟨70270005483152404223507747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46846670322101602815671831 70270005483152404223507747)
  ·
    refine ⟨105405008224728606335261621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70270005483152404223507747 105405008224728606335261621)
    ·
      refine ⟨9881719521068306843930777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105405008224728606335261621 9881719521068306843930777)
      ·
        refine ⟨7411289640801230132948083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9881719521068306843930777 7411289640801230132948083)
        ·
          refine ⟨11116934461201845199422125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411289640801230132948083 11116934461201845199422125)
          ·
            refine ⟨4168850422950691949783297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11116934461201845199422125 4168850422950691949783297)
            ·
              refine ⟨3126637817213018962337473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168850422950691949783297 3126637817213018962337473)
              ·
                refine ⟨2344978362909764221753105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126637817213018962337473 2344978362909764221753105)
                ·
                  refine ⟨1758733772182323166314829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344978362909764221753105 1758733772182323166314829)
                  ·
                    refine ⟨659525164568371187368061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1758733772182323166314829 659525164568371187368061)
                    ·
                      rfl

theorem cell22_1926631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1926631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926631 prefixEnd_1926631 := by exact prefixLift 1926631
  have htrace : WordTrace (prefixWord ++ tailWord_1926631) baseStart_1926631 baseEnd_1926631 := by
    simpa [prefixWord, tailWord_1926631, baseEnd_1926631] using wordTrace_append hprefix tailTrace_1926631
  have hstable : (prefixWord ++ tailWord_1926631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926631).length < 2 ^ (prefixWord ++ tailWord_1926631).sum := by decide
  have hdescent : baseEnd_1926631 < baseStart_1926631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926687 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_1926687 : Nat := 118140960795 + 1926687 * 2 ^ 59
def prefixEnd_1926687 : Nat := 4983230072969 + 3 ^ 40 * 1926687 * 2
def baseEnd_1926687 : Nat := 659544334512805707967889

theorem tailTrace_1926687 : CollatzResearch.WordTrace tailWord_1926687 prefixEnd_1926687 659544334512805707967889 := by
  unfold tailWord_1926687
  simp only [CollatzResearch.WordTrace]
  refine ⟨70272047970949525787546315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46848031980633017191697543 70272047970949525787546315)
  ·
    refine ⟨105408071956424288681319473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70272047970949525787546315 105408071956424288681319473)
    ·
      refine ⟨79056053967318216510989605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105408071956424288681319473 79056053967318216510989605)
      ·
        refine ⟨14823010118872165595810551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79056053967318216510989605 14823010118872165595810551)
        ·
          refine ⟨22234515178308248393715827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823010118872165595810551 22234515178308248393715827)
          ·
            refine ⟨33351772767462372590573741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22234515178308248393715827 33351772767462372590573741)
            ·
              refine ⟨12506914787798389721465153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33351772767462372590573741 12506914787798389721465153)
              ·
                refine ⟨9380186090848792291098865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12506914787798389721465153 9380186090848792291098865)
                ·
                  refine ⟨7035139568136594218324149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9380186090848792291098865 7035139568136594218324149)
                  ·
                    refine ⟨659544334512805707967889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7035139568136594218324149 659544334512805707967889)
                    ·
                      rfl

theorem cell22_1926687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_1926687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926687 prefixEnd_1926687 := by exact prefixLift 1926687
  have htrace : WordTrace (prefixWord ++ tailWord_1926687) baseStart_1926687 baseEnd_1926687 := by
    simpa [prefixWord, tailWord_1926687, baseEnd_1926687] using wordTrace_append hprefix tailTrace_1926687
  have hstable : (prefixWord ++ tailWord_1926687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926687).length < 2 ^ (prefixWord ++ tailWord_1926687).sum := by decide
  have hdescent : baseEnd_1926687 < baseStart_1926687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926689 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 5]
def baseStart_1926689 : Nat := 118140960795 + 1926689 * 2 ^ 59
def prefixEnd_1926689 : Nat := 4983230072969 + 3 ^ 40 * 1926689 * 2
def baseEnd_1926689 : Nat := 219848339717892789805961

theorem tailTrace_1926689 : CollatzResearch.WordTrace tailWord_1926689 prefixEnd_1926689 219848339717892789805961 := by
  unfold tailWord_1926689
  simp only [CollatzResearch.WordTrace]
  refine ⟨70272120916942280129119121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46848080611294853419412747 70272120916942280129119121)
  ·
    refine ⟨52704090687706710096839341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70272120916942280129119121 52704090687706710096839341)
    ·
      refine ⟨19764034007890016286314753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52704090687706710096839341 19764034007890016286314753)
      ·
        refine ⟨14823025505917512214736065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764034007890016286314753 14823025505917512214736065)
        ·
          refine ⟨11117269129438134161052049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14823025505917512214736065 11117269129438134161052049)
          ·
            refine ⟨8337951847078600620789037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117269129438134161052049 8337951847078600620789037)
            ·
              refine ⟨3126731942654475232795889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8337951847078600620789037 3126731942654475232795889)
              ·
                refine ⟨2345048956990856424596917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126731942654475232795889 2345048956990856424596917)
                ·
                  refine ⟨219848339717892789805961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2345048956990856424596917 219848339717892789805961)
                  ·
                    rfl

theorem cell22_1926689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_1926689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926689 prefixEnd_1926689 := by exact prefixLift 1926689
  have htrace : WordTrace (prefixWord ++ tailWord_1926689) baseStart_1926689 baseEnd_1926689 := by
    simpa [prefixWord, tailWord_1926689, baseEnd_1926689] using wordTrace_append hprefix tailTrace_1926689
  have hstable : (prefixWord ++ tailWord_1926689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926689).length < 2 ^ (prefixWord ++ tailWord_1926689).sum := by decide
  have hdescent : baseEnd_1926689 < baseStart_1926689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926719 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 1, 4]
def baseStart_1926719 : Nat := 118140960795 + 1926719 * 2 ^ 59
def prefixEnd_1926719 : Nat := 4983230072969 + 3 ^ 40 * 1926719 * 2
def baseEnd_1926719 : Nat := 659555288766768291167791

theorem tailTrace_1926719 : CollatzResearch.WordTrace tailWord_1926719 prefixEnd_1926719 659555288766768291167791 := by
  unfold tailWord_1926719
  simp only [CollatzResearch.WordTrace]
  refine ⟨70273215106833595252711211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46848810071222396835140807 70273215106833595252711211)
  ·
    refine ⟨105409822660250392879066817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70273215106833595252711211 105409822660250392879066817)
    ·
      refine ⟨79057366995187794659300113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105409822660250392879066817 79057366995187794659300113)
      ·
        refine ⟨59293025246390845994475085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79057366995187794659300113 59293025246390845994475085)
        ·
          refine ⟨22234884467396567247928157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59293025246390845994475085 22234884467396567247928157)
          ·
            refine ⟨8338081675273712717973059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22234884467396567247928157 8338081675273712717973059)
            ·
              refine ⟨12507122512910569076959589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338081675273712717973059 12507122512910569076959589)
              ·
                refine ⟨2345085471170731701929923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12507122512910569076959589 2345085471170731701929923)
                ·
                  refine ⟨3517628206756097552894885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345085471170731701929923 3517628206756097552894885)
                  ·
                    refine ⟨659555288766768291167791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517628206756097552894885 659555288766768291167791)
                    ·
                      rfl

theorem cell22_1926719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_1926719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926719 prefixEnd_1926719 := by exact prefixLift 1926719
  have htrace : WordTrace (prefixWord ++ tailWord_1926719) baseStart_1926719 baseEnd_1926719 := by
    simpa [prefixWord, tailWord_1926719, baseEnd_1926719] using wordTrace_append hprefix tailTrace_1926719
  have hstable : (prefixWord ++ tailWord_1926719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926719).length < 2 ^ (prefixWord ++ tailWord_1926719).sum := by decide
  have hdescent : baseEnd_1926719 < baseStart_1926719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926781 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1926781 : Nat := 118140960795 + 1926781 * 2 ^ 59
def prefixEnd_1926781 : Nat := 4983230072969 + 3 ^ 40 * 1926781 * 2
def baseEnd_1926781 : Nat := 659576512633820796117601

theorem tailTrace_1926781 : CollatzResearch.WordTrace tailWord_1926781 prefixEnd_1926781 659576512633820796117601 := by
  unfold tailWord_1926781
  simp only [CollatzResearch.WordTrace]
  refine ⟨70275476432608979841468197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46850317621739319894312131 70275476432608979841468197)
  ·
    refine ⟨13176651831114183720275287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70275476432608979841468197 13176651831114183720275287)
    ·
      refine ⟨19764977746671275580412931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13176651831114183720275287 19764977746671275580412931)
      ·
        refine ⟨29647466620006913370619397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19764977746671275580412931 29647466620006913370619397)
        ·
          refine ⟨5558899991251296256991137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29647466620006913370619397 5558899991251296256991137)
          ·
            refine ⟨4169174993438472192743353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558899991251296256991137 4169174993438472192743353)
            ·
              refine ⟨3126881245078854144557515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169174993438472192743353 3126881245078854144557515)
              ·
                refine ⟨4690321867618281216836273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126881245078854144557515 4690321867618281216836273)
                ·
                  refine ⟨3517741400713710912627205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690321867618281216836273 3517741400713710912627205)
                  ·
                    refine ⟨659576512633820796117601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517741400713710912627205 659576512633820796117601)
                    ·
                      rfl

theorem cell22_1926781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1926781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926781 prefixEnd_1926781 := by exact prefixLift 1926781
  have htrace : WordTrace (prefixWord ++ tailWord_1926781) baseStart_1926781 baseEnd_1926781 := by
    simpa [prefixWord, tailWord_1926781, baseEnd_1926781] using wordTrace_append hprefix tailTrace_1926781
  have hstable : (prefixWord ++ tailWord_1926781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926781).length < 2 ^ (prefixWord ++ tailWord_1926781).sum := by decide
  have hdescent : baseEnd_1926781 < baseStart_1926781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926802 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1926802 : Nat := 118140960795 + 1926802 * 2 ^ 59
def prefixEnd_1926802 : Nat := 4983230072969 + 3 ^ 40 * 1926802 * 2
def baseEnd_1926802 : Nat := 219861233787661247114179

theorem tailTrace_1926802 : CollatzResearch.WordTrace tailWord_1926802 prefixEnd_1926802 219861233787661247114179 := by
  unfold tailWord_1926802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569060591383225106995665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46850828243688600285321773 17569060591383225106995665)
  ·
    refine ⟨13176795443537418830246749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17569060591383225106995665 13176795443537418830246749)
    ·
      refine ⟨4941298291326532061342531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13176795443537418830246749 4941298291326532061342531)
      ·
        refine ⟨7411947436989798092013797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941298291326532061342531 7411947436989798092013797)
        ·
          refine ⟨1389740144435587142252587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7411947436989798092013797 1389740144435587142252587)
          ·
            refine ⟨2084610216653380713378881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389740144435587142252587 2084610216653380713378881)
            ·
              refine ⟨1563457662490035535034161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2084610216653380713378881 1563457662490035535034161)
              ·
                refine ⟨1172593246867526651275621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563457662490035535034161 1172593246867526651275621)
                ·
                  refine ⟨219861233787661247114179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1172593246867526651275621 219861233787661247114179)
                  ·
                    rfl

theorem cell22_1926802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1926802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926802 prefixEnd_1926802 := by exact prefixLift 1926802
  have htrace : WordTrace (prefixWord ++ tailWord_1926802) baseStart_1926802 baseEnd_1926802 := by
    simpa [prefixWord, tailWord_1926802, baseEnd_1926802] using wordTrace_append hprefix tailTrace_1926802
  have hstable : (prefixWord ++ tailWord_1926802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926802).length < 2 ^ (prefixWord ++ tailWord_1926802).sum := by decide
  have hdescent : baseEnd_1926802 < baseStart_1926802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926858 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_1926858 : Nat := 118140960795 + 1926858 * 2 ^ 59
def prefixEnd_1926858 : Nat := 4983230072969 + 3 ^ 40 * 1926858 * 2
def baseEnd_1926858 : Nat := 219867623769139420647455

theorem tailTrace_1926858 : CollatzResearch.WordTrace tailWord_1926858 prefixEnd_1926858 219867623769139420647455 := by
  unfold tailWord_1926858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569571213332505498005307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46852189902220014661347485 17569571213332505498005307)
  ·
    refine ⟨26354356819998758247007961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17569571213332505498005307 26354356819998758247007961)
    ·
      refine ⟨19765767614999068685255971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26354356819998758247007961 19765767614999068685255971)
      ·
        refine ⟨29648651422498603027883957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19765767614999068685255971 29648651422498603027883957)
        ·
          refine ⟨2779561070859244033864121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29648651422498603027883957 2779561070859244033864121)
          ·
            refine ⟨2084670803144433025398091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2779561070859244033864121 2084670803144433025398091)
            ·
              refine ⟨3127006204716649538097137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084670803144433025398091 3127006204716649538097137)
              ·
                refine ⟨2345254653537487153572853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127006204716649538097137 2345254653537487153572853)
                ·
                  refine ⟨219867623769139420647455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2345254653537487153572853 219867623769139420647455)
                  ·
                    rfl

theorem cell22_1926858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_1926858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926858 prefixEnd_1926858 := by exact prefixLift 1926858
  have htrace : WordTrace (prefixWord ++ tailWord_1926858) baseStart_1926858 baseEnd_1926858 := by
    simpa [prefixWord, tailWord_1926858, baseEnd_1926858] using wordTrace_append hprefix tailTrace_1926858
  have hstable : (prefixWord ++ tailWord_1926858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926858).length < 2 ^ (prefixWord ++ tailWord_1926858).sum := by decide
  have hdescent : baseEnd_1926858 < baseStart_1926858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926888 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_1926888 : Nat := 118140960795 + 1926888 * 2 ^ 59
def prefixEnd_1926888 : Nat := 4983230072969 + 3 ^ 40 * 1926888 * 2
def baseEnd_1926888 : Nat := 659613140920508183692273

theorem tailTrace_1926888 : CollatzResearch.WordTrace tailWord_1926888 prefixEnd_1926888 659613140920508183692273 := by
  unfold tailWord_1926888
  simp only [CollatzResearch.WordTrace]
  refine ⟨35139689521610668557806659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46852919362147558077075545 35139689521610668557806659)
  ·
    refine ⟨52709534282416002836709989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35139689521610668557806659 52709534282416002836709989)
    ·
      refine ⟨9883037677953000531883123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52709534282416002836709989 9883037677953000531883123)
      ·
        refine ⟨14824556516929500797824685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9883037677953000531883123 14824556516929500797824685)
        ·
          refine ⟨5559208693848562799184257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14824556516929500797824685 5559208693848562799184257)
          ·
            refine ⟨4169406520386422099388193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559208693848562799184257 4169406520386422099388193)
            ·
              refine ⟨3127054890289816574541145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169406520386422099388193 3127054890289816574541145)
              ·
                refine ⟨2345291167717362430905859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127054890289816574541145 2345291167717362430905859)
                ·
                  refine ⟨3517936751576043646358789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345291167717362430905859 3517936751576043646358789)
                  ·
                    refine ⟨659613140920508183692273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517936751576043646358789 659613140920508183692273)
                    ·
                      rfl

theorem cell22_1926888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_1926888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926888 prefixEnd_1926888 := by exact prefixLift 1926888
  have htrace : WordTrace (prefixWord ++ tailWord_1926888) baseStart_1926888 baseEnd_1926888 := by
    simpa [prefixWord, tailWord_1926888, baseEnd_1926888] using wordTrace_append hprefix tailTrace_1926888
  have hstable : (prefixWord ++ tailWord_1926888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926888).length < 2 ^ (prefixWord ++ tailWord_1926888).sum := by decide
  have hdescent : baseEnd_1926888 < baseStart_1926888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926899 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 1, 6]
def baseStart_1926899 : Nat := 118140960795 + 1926899 * 2 ^ 59
def prefixEnd_1926899 : Nat := 4983230072969 + 3 ^ 40 * 1926899 * 2
def baseEnd_1926899 : Nat := 659616906445307821667239

theorem tailTrace_1926899 : CollatzResearch.WordTrace tailWord_1926899 prefixEnd_1926899 659616906445307821667239 := by
  unfold tailWord_1926899
  simp only [CollatzResearch.WordTrace]
  refine ⟨70279780246181485994263751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46853186830787657329509167 70279780246181485994263751)
  ·
    refine ⟨105419670369272228991395627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70279780246181485994263751 105419670369272228991395627)
    ·
      refine ⟨158129505553908343487093441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105419670369272228991395627 158129505553908343487093441)
      ·
        refine ⟨118597129165431257615320081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158129505553908343487093441 118597129165431257615320081)
        ·
          refine ⟨88947846874073443211490061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118597129165431257615320081 88947846874073443211490061)
          ·
            refine ⟨33355442577777541204308773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88947846874073443211490061 33355442577777541204308773)
            ·
              refine ⟨6254145483333288975807895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33355442577777541204308773 6254145483333288975807895)
              ·
                refine ⟨9381218224999933463711843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254145483333288975807895 9381218224999933463711843)
                ·
                  refine ⟨14071827337499900195567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381218224999933463711843 14071827337499900195567765)
                  ·
                    refine ⟨659616906445307821667239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14071827337499900195567765 659616906445307821667239)
                    ·
                      rfl

theorem cell22_1926899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_1926899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926899 prefixEnd_1926899 := by exact prefixLift 1926899
  have htrace : WordTrace (prefixWord ++ tailWord_1926899) baseStart_1926899 baseEnd_1926899 := by
    simpa [prefixWord, tailWord_1926899, baseEnd_1926899] using wordTrace_append hprefix tailTrace_1926899
  have hstable : (prefixWord ++ tailWord_1926899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926899).length < 2 ^ (prefixWord ++ tailWord_1926899).sum := by decide
  have hdescent : baseEnd_1926899 < baseStart_1926899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926916 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1926916 : Nat := 118140960795 + 1926916 * 2 ^ 59
def prefixEnd_1926916 : Nat := 4983230072969 + 3 ^ 40 * 1926916 * 2
def baseEnd_1926916 : Nat := 659622725892725443992187

theorem tailTrace_1926916 : CollatzResearch.WordTrace tailWord_1926916 prefixEnd_1926916 659622725892725443992187 := by
  unfold tailWord_1926916
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140200143559948948816301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46853600191413265265088401 35140200143559948948816301)
  ·
    refine ⟨13177575053834980855806113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35140200143559948948816301 13177575053834980855806113)
    ·
      refine ⟨9883181290376235641854585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13177575053834980855806113 9883181290376235641854585)
      ·
        refine ⟨7412385967782176731390939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9883181290376235641854585 7412385967782176731390939)
        ·
          refine ⟨11118578951673265097086409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412385967782176731390939 11118578951673265097086409)
          ·
            refine ⟨8338934213754948822814807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11118578951673265097086409 8338934213754948822814807)
            ·
              refine ⟨12508401320632423234222211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338934213754948822814807 12508401320632423234222211)
              ·
                refine ⟨18762601980948634851333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12508401320632423234222211 18762601980948634851333317)
                ·
                  refine ⟨3517987871427869034624997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18762601980948634851333317 3517987871427869034624997)
                  ·
                    refine ⟨659622725892725443992187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517987871427869034624997 659622725892725443992187)
                    ·
                      rfl

theorem cell22_1926916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1926916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926916 prefixEnd_1926916 := by exact prefixLift 1926916
  have htrace : WordTrace (prefixWord ++ tailWord_1926916) baseStart_1926916 baseEnd_1926916 := by
    simpa [prefixWord, tailWord_1926916, baseEnd_1926916] using wordTrace_append hprefix tailTrace_1926916
  have hstable : (prefixWord ++ tailWord_1926916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926916).length < 2 ^ (prefixWord ++ tailWord_1926916).sum := by decide
  have hdescent : baseEnd_1926916 < baseStart_1926916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926935 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 2, 3]
def baseStart_1926935 : Nat := 118140960795 + 1926935 * 2 ^ 59
def prefixEnd_1926935 : Nat := 4983230072969 + 3 ^ 40 * 1926935 * 2
def baseEnd_1926935 : Nat := 659629229981015727767129

theorem tailTrace_1926935 : CollatzResearch.WordTrace tailWord_1926935 prefixEnd_1926935 659629229981015727767129 := by
  unfold tailWord_1926935
  simp only [CollatzResearch.WordTrace]
  refine ⟨70281093274051064142574259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46854062182700709428382839 70281093274051064142574259)
  ·
    refine ⟨105421639911076596213861389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70281093274051064142574259 105421639911076596213861389)
    ·
      refine ⟨39533114966653723580198021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105421639911076596213861389 39533114966653723580198021)
      ·
        refine ⟨7412459056247573171287129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39533114966653723580198021 7412459056247573171287129)
        ·
          refine ⟨5559344292185679878465347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7412459056247573171287129 5559344292185679878465347)
          ·
            refine ⟨8339016438278519817698021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559344292185679878465347 8339016438278519817698021)
            ·
              refine ⟨1563565582177222465818379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8339016438278519817698021 1563565582177222465818379)
              ·
                refine ⟨2345348373265833698727569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563565582177222465818379 2345348373265833698727569)
                ·
                  refine ⟨1759011279949375274045677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345348373265833698727569 1759011279949375274045677)
                  ·
                    refine ⟨659629229981015727767129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759011279949375274045677 659629229981015727767129)
                    ·
                      rfl

theorem cell22_1926935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_1926935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926935 prefixEnd_1926935 := by exact prefixLift 1926935
  have htrace : WordTrace (prefixWord ++ tailWord_1926935) baseStart_1926935 baseEnd_1926935 := by
    simpa [prefixWord, tailWord_1926935, baseEnd_1926935] using wordTrace_append hprefix tailTrace_1926935
  have hstable : (prefixWord ++ tailWord_1926935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926935).length < 2 ^ (prefixWord ++ tailWord_1926935).sum := by decide
  have hdescent : baseEnd_1926935 < baseStart_1926935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927068 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1927068 : Nat := 118140960795 + 1927068 * 2 ^ 59
def prefixEnd_1927068 : Nat := 4983230072969 + 3 ^ 40 * 1927068 * 2
def baseEnd_1927068 : Nat := 659674758599047714191721

theorem tailTrace_1927068 : CollatzResearch.WordTrace tailWord_1927068 prefixEnd_1927068 659674758599047714191721 := by
  unfold tailWord_1927068
  simp only [CollatzResearch.WordTrace]
  refine ⟨35142972091284613928582929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46857296121712818571443905 35142972091284613928582929)
  ·
    refine ⟨26357229068463460446437197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35142972091284613928582929 26357229068463460446437197)
    ·
      refine ⟨9883960900673797667413949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26357229068463460446437197 9883960900673797667413949)
      ·
        refine ⟨3706485337752674125280231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9883960900673797667413949 3706485337752674125280231)
        ·
          refine ⟨5559728006629011187920347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706485337752674125280231 5559728006629011187920347)
          ·
            refine ⟨8339592009943516781880521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559728006629011187920347 8339592009943516781880521)
            ·
              refine ⟨6254694007457637586410391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339592009943516781880521 6254694007457637586410391)
              ·
                refine ⟨9382041011186456379615587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254694007457637586410391 9382041011186456379615587)
                ·
                  refine ⟨14073061516779684569423381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9382041011186456379615587 14073061516779684569423381)
                  ·
                    refine ⟨659674758599047714191721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14073061516779684569423381 659674758599047714191721)
                    ·
                      rfl

theorem cell22_1927068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1927068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927068 prefixEnd_1927068 := by exact prefixLift 1927068
  have htrace : WordTrace (prefixWord ++ tailWord_1927068) baseStart_1927068 baseEnd_1927068 := by
    simpa [prefixWord, tailWord_1927068, baseEnd_1927068] using wordTrace_append hprefix tailTrace_1927068
  have hstable : (prefixWord ++ tailWord_1927068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927068).length < 2 ^ (prefixWord ++ tailWord_1927068).sum := by decide
  have hdescent : baseEnd_1927068 < baseStart_1927068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927096 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_1927096 : Nat := 118140960795 + 1927096 * 2 ^ 59
def prefixEnd_1927096 : Nat := 4983230072969 + 3 ^ 40 * 1927096 * 2
def baseEnd_1927096 : Nat := 659684343571264974491635

theorem tailTrace_1927096 : CollatzResearch.WordTrace tailWord_1927096 prefixEnd_1927096 659684343571264974491635 := by
  unfold tailWord_1927096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35143482713233894319592571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46857976950978525759456761 35143482713233894319592571)
  ·
    refine ⟨52715224069850841479388857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35143482713233894319592571 52715224069850841479388857)
    ·
      refine ⟨39536418052388131109541643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52715224069850841479388857 39536418052388131109541643)
      ·
        refine ⟨59304627078582196664312465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39536418052388131109541643 59304627078582196664312465)
        ·
          refine ⟨44478470308936647498234349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59304627078582196664312465 44478470308936647498234349)
          ·
            refine ⟨16679426365851242811837881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44478470308936647498234349 16679426365851242811837881)
            ·
              refine ⟨12509569774388432108878411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16679426365851242811837881 12509569774388432108878411)
              ·
                refine ⟨18764354661582648163317617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12509569774388432108878411 18764354661582648163317617)
                ·
                  refine ⟨14073265996186986122488213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18764354661582648163317617 14073265996186986122488213)
                  ·
                    refine ⟨659684343571264974491635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14073265996186986122488213 659684343571264974491635)
                    ·
                      rfl

theorem cell22_1927096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_1927096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927096 prefixEnd_1927096 := by exact prefixLift 1927096
  have htrace : WordTrace (prefixWord ++ tailWord_1927096) baseStart_1927096 baseEnd_1927096 := by
    simpa [prefixWord, tailWord_1927096, baseEnd_1927096] using wordTrace_append hprefix tailTrace_1927096
  have hstable : (prefixWord ++ tailWord_1927096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927096).length < 2 ^ (prefixWord ++ tailWord_1927096).sum := by decide
  have hdescent : baseEnd_1927096 < baseStart_1927096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927098 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1927098 : Nat := 118140960795 + 1927098 * 2 ^ 59
def prefixEnd_1927098 : Nat := 4983230072969 + 3 ^ 40 * 1927098 * 2
def baseEnd_1927098 : Nat := 659685028212137635941629

theorem tailTrace_1927098 : CollatzResearch.WordTrace tailWord_1927098 prefixEnd_1927098 659685028212137635941629 := by
  unfold tailWord_1927098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17571759593115135745189487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46858025581640361987171965 17571759593115135745189487)
  ·
    refine ⟨26357639389672703617784231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17571759593115135745189487 26357639389672703617784231)
    ·
      refine ⟨39536459084509055426676347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26357639389672703617784231 39536459084509055426676347)
      ·
        refine ⟨59304688626763583140014521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39536459084509055426676347 59304688626763583140014521)
        ·
          refine ⟨44478516470072687355010891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59304688626763583140014521 44478516470072687355010891)
          ·
            refine ⟨66717774705109031032516337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44478516470072687355010891 66717774705109031032516337)
            ·
              refine ⟨50038331028831773274387253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66717774705109031032516337 50038331028831773274387253)
              ·
                refine ⟨4691093533952978744473805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50038331028831773274387253 4691093533952978744473805)
                ·
                  refine ⟨1759160075232367029177677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4691093533952978744473805 1759160075232367029177677)
                  ·
                    refine ⟨659685028212137635941629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759160075232367029177677 659685028212137635941629)
                    ·
                      rfl

theorem cell22_1927098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1927098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927098 prefixEnd_1927098 := by exact prefixLift 1927098
  have htrace : WordTrace (prefixWord ++ tailWord_1927098) baseStart_1927098 baseEnd_1927098 := by
    simpa [prefixWord, tailWord_1927098, baseEnd_1927098] using wordTrace_append hprefix tailTrace_1927098
  have hstable : (prefixWord ++ tailWord_1927098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927098).length < 2 ^ (prefixWord ++ tailWord_1927098).sum := by decide
  have hdescent : baseEnd_1927098 < baseStart_1927098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927100 : List Nat := [2, 2, 2, 5, 1, 1, 2, 7]
def baseStart_1927100 : Nat := 118140960795 + 1927100 * 2 ^ 59
def prefixEnd_1927100 : Nat := 4983230072969 + 3 ^ 40 * 1927100 * 2
def baseEnd_1927100 : Nat := 73298412539223366376847

theorem tailTrace_1927100 : CollatzResearch.WordTrace tailWord_1927100 prefixEnd_1927100 73298412539223366376847 := by
  unfold tailWord_1927100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35143555659226648661165377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46858074212302198214887169 35143555659226648661165377)
  ·
    refine ⟨26357666744419986495874033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35143555659226648661165377 26357666744419986495874033)
    ·
      refine ⟨19768250058314989871905525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26357666744419986495874033 19768250058314989871905525)
      ·
        refine ⟨1853273442967030300491143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19768250058314989871905525 1853273442967030300491143)
        ·
          refine ⟨2779910164450545450736715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853273442967030300491143 2779910164450545450736715)
          ·
            refine ⟨4169865246675818176105073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779910164450545450736715 4169865246675818176105073)
            ·
              refine ⟨3127398935006863632078805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169865246675818176105073 3127398935006863632078805)
              ·
                refine ⟨73298412539223366376847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3127398935006863632078805 73298412539223366376847)
                ·
                  rfl

theorem cell22_1927100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 7].length) (baseStart_1927100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927100 prefixEnd_1927100 := by exact prefixLift 1927100
  have htrace : WordTrace (prefixWord ++ tailWord_1927100) baseStart_1927100 baseEnd_1927100 := by
    simpa [prefixWord, tailWord_1927100, baseEnd_1927100] using wordTrace_append hprefix tailTrace_1927100
  have hstable : (prefixWord ++ tailWord_1927100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927100).length < 2 ^ (prefixWord ++ tailWord_1927100).sum := by decide
  have hdescent : baseEnd_1927100 < baseStart_1927100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927173 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 6]
def baseStart_1927173 : Nat := 118140960795 + 1927173 * 2 ^ 59
def prefixEnd_1927173 : Nat := 4983230072969 + 3 ^ 40 * 1927173 * 2
def baseEnd_1927173 : Nat := 219903567414954146772133

theorem tailTrace_1927173 : CollatzResearch.WordTrace tailWord_1927173 prefixEnd_1927173 219903567414954146772133 := by
  unfold tailWord_1927173
  simp only [CollatzResearch.WordTrace]
  refine ⟨70289773847188830789738173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46859849231459220526492115 70289773847188830789738173)
  ·
    refine ⟨26358665192695811546151815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70289773847188830789738173 26358665192695811546151815)
    ·
      refine ⟨39537997789043717319227723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26358665192695811546151815 39537997789043717319227723)
      ·
        refine ⟨59306996683565575978841585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39537997789043717319227723 59306996683565575978841585)
        ·
          refine ⟨44480247512674181984131189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59306996683565575978841585 44480247512674181984131189)
          ·
            refine ⟨4170023204313204561012299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44480247512674181984131189 4170023204313204561012299)
            ·
              refine ⟨6255034806469806841518449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170023204313204561012299 6255034806469806841518449)
              ·
                refine ⟨4691276104852355131138837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6255034806469806841518449 4691276104852355131138837)
                ·
                  refine ⟨219903567414954146772133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4691276104852355131138837 219903567414954146772133)
                  ·
                    rfl

theorem cell22_1927173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_1927173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927173 prefixEnd_1927173 := by exact prefixLift 1927173
  have htrace : WordTrace (prefixWord ++ tailWord_1927173) baseStart_1927173 baseEnd_1927173 := by
    simpa [prefixWord, tailWord_1927173, baseEnd_1927173] using wordTrace_append hprefix tailTrace_1927173
  have hstable : (prefixWord ++ tailWord_1927173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927173).length < 2 ^ (prefixWord ++ tailWord_1927173).sum := by decide
  have hdescent : baseEnd_1927173 < baseStart_1927173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927203 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 4, 4]
def baseStart_1927203 : Nat := 118140960795 + 1927203 * 2 ^ 59
def prefixEnd_1927203 : Nat := 4983230072969 + 3 ^ 40 * 1927203 * 2
def baseEnd_1927203 : Nat := 659720971857952362066307

theorem tailTrace_1927203 : CollatzResearch.WordTrace tailWord_1927203 prefixEnd_1927203 659720971857952362066307 := by
  unfold tailWord_1927203
  simp only [CollatzResearch.WordTrace]
  refine ⟨70290868037080145913330263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46860578691386763942220175 70290868037080145913330263)
  ·
    refine ⟨105436302055620218869995395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70290868037080145913330263 105436302055620218869995395)
    ·
      refine ⟨158154453083430328304993093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105436302055620218869995395 158154453083430328304993093)
      ·
        refine ⟨29653959953143186557186205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158154453083430328304993093 29653959953143186557186205)
        ·
          refine ⟨11120234982428694958944827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29653959953143186557186205 11120234982428694958944827)
          ·
            refine ⟨16680352473643042438417241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11120234982428694958944827 16680352473643042438417241)
            ·
              refine ⟨12510264355232281828812931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16680352473643042438417241 12510264355232281828812931)
              ·
                refine ⟨18765396532848422743219397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12510264355232281828812931 18765396532848422743219397)
                ·
                  refine ⟨3518511849909079264353637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18765396532848422743219397 3518511849909079264353637)
                  ·
                    refine ⟨659720971857952362066307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3518511849909079264353637 659720971857952362066307)
                    ·
                      rfl

theorem cell22_1927203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_1927203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927203 prefixEnd_1927203 := by exact prefixLift 1927203
  have htrace : WordTrace (prefixWord ++ tailWord_1927203) baseStart_1927203 baseEnd_1927203 := by
    simpa [prefixWord, tailWord_1927203, baseEnd_1927203] using wordTrace_append hprefix tailTrace_1927203
  have hstable : (prefixWord ++ tailWord_1927203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927203).length < 2 ^ (prefixWord ++ tailWord_1927203).sum := by decide
  have hdescent : baseEnd_1927203 < baseStart_1927203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927205 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_1927205 : Nat := 118140960795 + 1927205 * 2 ^ 59
def prefixEnd_1927205 : Nat := 4983230072969 + 3 ^ 40 * 1927205 * 2
def baseEnd_1927205 : Nat := 659721656498825023516301

theorem tailTrace_1927205 : CollatzResearch.WordTrace tailWord_1927205 prefixEnd_1927205 659721656498825023516301 := by
  unfold tailWord_1927205
  simp only [CollatzResearch.WordTrace]
  refine ⟨70290940983072900254903069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46860627322048600169935379 70290940983072900254903069)
  ·
    refine ⟨26359102868652337595588651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70290940983072900254903069 26359102868652337595588651)
    ·
      refine ⟨39538654302978506393382977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26359102868652337595588651 39538654302978506393382977)
      ·
        refine ⟨29653990727233879795037233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39538654302978506393382977 29653990727233879795037233)
        ·
          refine ⟨22240493045425409846277925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29653990727233879795037233 22240493045425409846277925)
          ·
            refine ⟨4170092446017264346177111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22240493045425409846277925 4170092446017264346177111)
            ·
              refine ⟨6255138669025896519265667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170092446017264346177111 6255138669025896519265667)
              ·
                refine ⟨9382708003538844778898501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6255138669025896519265667 9382708003538844778898501)
                ·
                  refine ⟨1759257750663533396043469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9382708003538844778898501 1759257750663533396043469)
                  ·
                    refine ⟨659721656498825023516301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759257750663533396043469 659721656498825023516301)
                    ·
                      rfl

theorem cell22_1927205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_1927205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927205 prefixEnd_1927205 := by exact prefixLift 1927205
  have htrace : WordTrace (prefixWord ++ tailWord_1927205) baseStart_1927205 baseEnd_1927205 := by
    simpa [prefixWord, tailWord_1927205, baseEnd_1927205] using wordTrace_append hprefix tailTrace_1927205
  have hstable : (prefixWord ++ tailWord_1927205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927205).length < 2 ^ (prefixWord ++ tailWord_1927205).sum := by decide
  have hdescent : baseEnd_1927205 < baseStart_1927205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927207 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 6]
def baseStart_1927207 : Nat := 118140960795 + 1927207 * 2 ^ 59
def prefixEnd_1927207 : Nat := 4983230072969 + 3 ^ 40 * 1927207 * 2
def baseEnd_1927207 : Nat := 219907447046565894988765

theorem tailTrace_1927207 : CollatzResearch.WordTrace tailWord_1927207 prefixEnd_1927207 219907447046565894988765 := by
  unfold tailWord_1927207
  simp only [CollatzResearch.WordTrace]
  refine ⟨70291013929065654596475875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46860675952710436397650583 70291013929065654596475875)
  ·
    refine ⟨105436520893598481894713813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70291013929065654596475875 105436520893598481894713813)
    ·
      refine ⟨2471168458443714419407355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 105436520893598481894713813 2471168458443714419407355)
      ·
        refine ⟨3706752687665571629111033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471168458443714419407355 3706752687665571629111033)
        ·
          refine ⟨2780064515749178721833275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3706752687665571629111033 2780064515749178721833275)
          ·
            refine ⟨4170096773623768082749913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780064515749178721833275 4170096773623768082749913)
            ·
              refine ⟨3127572580217826062062435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4170096773623768082749913 3127572580217826062062435)
              ·
                refine ⟨4691358870326739093093653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127572580217826062062435 4691358870326739093093653)
                ·
                  refine ⟨219907447046565894988765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4691358870326739093093653 219907447046565894988765)
                  ·
                    rfl

theorem cell22_1927207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 6].length) (baseStart_1927207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927207 prefixEnd_1927207 := by exact prefixLift 1927207
  have htrace : WordTrace (prefixWord ++ tailWord_1927207) baseStart_1927207 baseEnd_1927207 := by
    simpa [prefixWord, tailWord_1927207, baseEnd_1927207] using wordTrace_append hprefix tailTrace_1927207
  have hstable : (prefixWord ++ tailWord_1927207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927207).length < 2 ^ (prefixWord ++ tailWord_1927207).sum := by decide
  have hdescent : baseEnd_1927207 < baseStart_1927207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927254 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1927254 : Nat := 118140960795 + 1927254 * 2 ^ 59
def prefixEnd_1927254 : Nat := 4983230072969 + 3 ^ 40 * 1927254 * 2
def baseEnd_1927254 : Nat := 659738430200205229041151

theorem tailTrace_1927254 : CollatzResearch.WordTrace tailWord_1927254 prefixEnd_1927254 659738430200205229041151 := by
  unfold tailWord_1927254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393295509993461351464801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46861818773263587748957877 4393295509993461351464801)
  ·
    refine ⟨3294971632495096013598601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4393295509993461351464801 3294971632495096013598601)
    ·
      refine ⟨2471228724371322010198951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3294971632495096013598601 2471228724371322010198951)
      ·
        refine ⟨3706843086556983015298427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471228724371322010198951 3706843086556983015298427)
        ·
          refine ⟨5560264629835474522947641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706843086556983015298427 5560264629835474522947641)
          ·
            refine ⟨4170198472376605892210731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5560264629835474522947641 4170198472376605892210731)
            ·
              refine ⟨6255297708564908838316097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170198472376605892210731 6255297708564908838316097)
              ·
                refine ⟨4691473281423681628737073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6255297708564908838316097 4691473281423681628737073)
                ·
                  refine ⟨3518604961067761221552805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4691473281423681628737073 3518604961067761221552805)
                  ·
                    refine ⟨659738430200205229041151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3518604961067761221552805 659738430200205229041151)
                    ·
                      rfl

theorem cell22_1927254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1927254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927254 prefixEnd_1927254 := by exact prefixLift 1927254
  have htrace : WordTrace (prefixWord ++ tailWord_1927254) baseStart_1927254 baseEnd_1927254 := by
    simpa [prefixWord, tailWord_1927254, baseEnd_1927254] using wordTrace_append hprefix tailTrace_1927254
  have hstable : (prefixWord ++ tailWord_1927254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927254).length < 2 ^ (prefixWord ++ tailWord_1927254).sum := by decide
  have hdescent : baseEnd_1927254 < baseStart_1927254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927267 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 1, 3]
def baseStart_1927267 : Nat := 118140960795 + 1927267 * 2 ^ 59
def prefixEnd_1927267 : Nat := 4983230072969 + 3 ^ 40 * 1927267 * 2
def baseEnd_1927267 : Nat := 659742880365877528466111

theorem tailTrace_1927267 : CollatzResearch.WordTrace tailWord_1927267 prefixEnd_1927267 659742880365877528466111 := by
  unfold tailWord_1927267
  simp only [CollatzResearch.WordTrace]
  refine ⟨70293202308848284843660055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46862134872565523229106703 70293202308848284843660055)
  ·
    refine ⟨105439803463272427265490083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70293202308848284843660055 105439803463272427265490083)
    ·
      refine ⟨158159705194908640898235125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105439803463272427265490083 158159705194908640898235125)
      ·
        refine ⟨14827472362022685084209543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158159705194908640898235125 14827472362022685084209543)
        ·
          refine ⟨22241208543034027626314315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14827472362022685084209543 22241208543034027626314315)
          ·
            refine ⟨33361812814551041439471473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22241208543034027626314315 33361812814551041439471473)
            ·
              refine ⟨25021359610913281079603605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33361812814551041439471473 25021359610913281079603605)
              ·
                refine ⟨1172876231761560050606419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25021359610913281079603605 1172876231761560050606419)
                ·
                  refine ⟨1759314347642340075909629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172876231761560050606419 1759314347642340075909629)
                  ·
                    refine ⟨659742880365877528466111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759314347642340075909629 659742880365877528466111)
                    ·
                      rfl

theorem cell22_1927267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 3].length) (baseStart_1927267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927267 prefixEnd_1927267 := by exact prefixLift 1927267
  have htrace : WordTrace (prefixWord ++ tailWord_1927267) baseStart_1927267 baseEnd_1927267 := by
    simpa [prefixWord, tailWord_1927267, baseEnd_1927267] using wordTrace_append hprefix tailTrace_1927267
  have hstable : (prefixWord ++ tailWord_1927267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927267).length < 2 ^ (prefixWord ++ tailWord_1927267).sum := by decide
  have hdescent : baseEnd_1927267 < baseStart_1927267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927280 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_1927280 : Nat := 118140960795 + 1927280 * 2 ^ 59
def prefixEnd_1927280 : Nat := 4983230072969 + 3 ^ 40 * 1927280 * 2
def baseEnd_1927280 : Nat := 219915776843849942630357

theorem tailTrace_1927280 : CollatzResearch.WordTrace tailWord_1927280 prefixEnd_1927280 219915776843849942630357 := by
  unfold tailWord_1927280
  simp only [CollatzResearch.WordTrace]
  refine ⟨35146838228900594031941647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46862450971867458709255529 35146838228900594031941647)
  ·
    refine ⟨52720257343350891047912471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35146838228900594031941647 52720257343350891047912471)
    ·
      refine ⟨79080386015026336571868707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52720257343350891047912471 79080386015026336571868707)
      ·
        refine ⟨118620579022539504857803061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79080386015026336571868707 118620579022539504857803061)
        ·
          refine ⟨11120679283363078580419037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118620579022539504857803061 11120679283363078580419037)
          ·
            refine ⟨4170254731261154467657139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11120679283363078580419037 4170254731261154467657139)
            ·
              refine ⟨6255382096891731701485709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170254731261154467657139 6255382096891731701485709)
              ·
                refine ⟨2345768286334399388057141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6255382096891731701485709 2345768286334399388057141)
                ·
                  refine ⟨219915776843849942630357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2345768286334399388057141 219915776843849942630357)
                  ·
                    rfl

theorem cell22_1927280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_1927280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927280 prefixEnd_1927280 := by exact prefixLift 1927280
  have htrace : WordTrace (prefixWord ++ tailWord_1927280) baseStart_1927280 baseEnd_1927280 := by
    simpa [prefixWord, tailWord_1927280, baseEnd_1927280] using wordTrace_append hprefix tailTrace_1927280
  have hstable : (prefixWord ++ tailWord_1927280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927280).length < 2 ^ (prefixWord ++ tailWord_1927280).sum := by decide
  have hdescent : baseEnd_1927280 < baseStart_1927280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927323 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_1927323 : Nat := 118140960795 + 1927323 * 2 ^ 59
def prefixEnd_1927323 : Nat := 4983230072969 + 3 ^ 40 * 1927323 * 2
def baseEnd_1927323 : Nat := 659762050310312049065939

theorem tailTrace_1927323 : CollatzResearch.WordTrace tailWord_1927323 prefixEnd_1927323 659762050310312049065939 := by
  unfold tailWord_1927323
  simp only [CollatzResearch.WordTrace]
  refine ⟨70295244796645406407698623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46863496531096937605132415 70295244796645406407698623)
  ·
    refine ⟨105442867194968109611547935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70295244796645406407698623 105442867194968109611547935)
    ·
      refine ⟨158164300792452164417321903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105442867194968109611547935 158164300792452164417321903)
      ·
        refine ⟨237246451188678246625982855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158164300792452164417321903 237246451188678246625982855)
        ·
          refine ⟨355869676783017369938974283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237246451188678246625982855 355869676783017369938974283)
          ·
            refine ⟨533804515174526054908461425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355869676783017369938974283 533804515174526054908461425)
            ·
              refine ⟨400353386380894541181346069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533804515174526054908461425 400353386380894541181346069)
              ·
                refine ⟨18766564986604431617875597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 400353386380894541181346069 18766564986604431617875597)
                ·
                  refine ⟨7037461869976661856703349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18766564986604431617875597 7037461869976661856703349)
                  ·
                    refine ⟨659762050310312049065939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7037461869976661856703349 659762050310312049065939)
                    ·
                      rfl

theorem cell22_1927323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_1927323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927323 prefixEnd_1927323 := by exact prefixLift 1927323
  have htrace : WordTrace (prefixWord ++ tailWord_1927323) baseStart_1927323 baseEnd_1927323 := by
    simpa [prefixWord, tailWord_1927323, baseEnd_1927323] using wordTrace_append hprefix tailTrace_1927323
  have hstable : (prefixWord ++ tailWord_1927323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927323).length < 2 ^ (prefixWord ++ tailWord_1927323).sum := by decide
  have hdescent : baseEnd_1927323 < baseStart_1927323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927374 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_1927374 : Nat := 118140960795 + 1927374 * 2 ^ 59
def prefixEnd_1927374 : Nat := 4983230072969 + 3 ^ 40 * 1927374 * 2
def baseEnd_1927374 : Nat := 659779508652564916040783

theorem tailTrace_1927374 : CollatzResearch.WordTrace tailWord_1927374 prefixEnd_1927374 659779508652564916040783 := by
  unfold tailWord_1927374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787138114932580264725647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46864736612973761411870117 8787138114932580264725647)
  ·
    refine ⟨13180707172398870397088471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8787138114932580264725647 13180707172398870397088471)
    ·
      refine ⟨19771060758598305595632707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13180707172398870397088471 19771060758598305595632707)
      ·
        refine ⟨29656591137897458393449061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19771060758598305595632707 29656591137897458393449061)
        ·
          refine ⟨5560610838355773448771699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29656591137897458393449061 5560610838355773448771699)
          ·
            refine ⟨8340916257533660173157549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560610838355773448771699 8340916257533660173157549)
            ·
              refine ⟨3127843596575122564934081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8340916257533660173157549 3127843596575122564934081)
              ·
                refine ⟨2345882697431341923700561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127843596575122564934081 2345882697431341923700561)
                ·
                  refine ⟨1759412023073506442775421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345882697431341923700561 1759412023073506442775421)
                  ·
                    refine ⟨659779508652564916040783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759412023073506442775421 659779508652564916040783)
                    ·
                      rfl

theorem cell22_1927374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_1927374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927374 prefixEnd_1927374 := by exact prefixLift 1927374
  have htrace : WordTrace (prefixWord ++ tailWord_1927374) baseStart_1927374 baseEnd_1927374 := by
    simpa [prefixWord, tailWord_1927374, baseEnd_1927374] using wordTrace_append hprefix tailTrace_1927374
  have hstable : (prefixWord ++ tailWord_1927374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927374).length < 2 ^ (prefixWord ++ tailWord_1927374).sum := by decide
  have hdescent : baseEnd_1927374 < baseStart_1927374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927402 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1927402 : Nat := 118140960795 + 1927402 * 2 ^ 59
def prefixEnd_1927402 : Nat := 4983230072969 + 3 ^ 40 * 1927402 * 2
def baseEnd_1927402 : Nat := 659789093624782176340697

theorem tailTrace_1927402 : CollatzResearch.WordTrace tailWord_1927402 prefixEnd_1927402 659789093624782176340697 := by
  unfold tailWord_1927402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17574531540839800724956115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46865417442239468599882973 17574531540839800724956115)
  ·
    refine ⟨26361797311259701087434173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17574531540839800724956115 26361797311259701087434173)
    ·
      refine ⟨9885673991722387907787815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26361797311259701087434173 9885673991722387907787815)
      ·
        refine ⟨14828510987583581861681723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885673991722387907787815 14828510987583581861681723)
        ·
          refine ⟨22242766481375372792522585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14828510987583581861681723 22242766481375372792522585)
          ·
            refine ⟨16682074861031529594391939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22242766481375372792522585 16682074861031529594391939)
            ·
              refine ⟨25023112291547294391587909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16682074861031529594391939 25023112291547294391587909)
              ·
                refine ⟨4691833554665117698422733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25023112291547294391587909 4691833554665117698422733)
                ·
                  refine ⟨1759437582999419136908525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4691833554665117698422733 1759437582999419136908525)
                  ·
                    refine ⟨659789093624782176340697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759437582999419136908525 659789093624782176340697)
                    ·
                      rfl

theorem cell22_1927402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1927402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927402 prefixEnd_1927402 := by exact prefixLift 1927402
  have htrace : WordTrace (prefixWord ++ tailWord_1927402) baseStart_1927402 baseEnd_1927402 := by
    simpa [prefixWord, tailWord_1927402, baseEnd_1927402] using wordTrace_append hprefix tailTrace_1927402
  have hstable : (prefixWord ++ tailWord_1927402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927402).length < 2 ^ (prefixWord ++ tailWord_1927402).sum := by decide
  have hdescent : baseEnd_1927402 < baseStart_1927402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927436 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_1927436 : Nat := 118140960795 + 1927436 * 2 ^ 59
def prefixEnd_1927436 : Nat := 4983230072969 + 3 ^ 40 * 1927436 * 2
def baseEnd_1927436 : Nat := 659800732519617420990593

theorem tailTrace_1927436 : CollatzResearch.WordTrace tailWord_1927436 prefixEnd_1927436 659800732519617420990593 := by
  unfold tailWord_1927436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35149683122618013353281081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46866244163490684471041441 35149683122618013353281081)
  ·
    refine ⟨26362262341963510014960811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35149683122618013353281081 26362262341963510014960811)
    ·
      refine ⟨39543393512945265022441217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26362262341963510014960811 39543393512945265022441217)
      ·
        refine ⟨29657545134708948766830913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39543393512945265022441217 29657545134708948766830913)
        ·
          refine ⟨22243158851031711575123185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29657545134708948766830913 22243158851031711575123185)
          ·
            refine ⟨16682369138273783681342389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22243158851031711575123185 16682369138273783681342389)
            ·
              refine ⟨1563972106713167220125849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16682369138273783681342389 1563972106713167220125849)
              ·
                refine ⟨1172979080034875415094387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563972106713167220125849 1172979080034875415094387)
                ·
                  refine ⟨1759468620052313122641581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172979080034875415094387 1759468620052313122641581)
                  ·
                    refine ⟨659800732519617420990593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759468620052313122641581 659800732519617420990593)
                    ·
                      rfl

theorem cell22_1927436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_1927436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927436 prefixEnd_1927436 := by exact prefixLift 1927436
  have htrace : WordTrace (prefixWord ++ tailWord_1927436) baseStart_1927436 baseEnd_1927436 := by
    simpa [prefixWord, tailWord_1927436, baseEnd_1927436] using wordTrace_append hprefix tailTrace_1927436
  have hstable : (prefixWord ++ tailWord_1927436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927436).length < 2 ^ (prefixWord ++ tailWord_1927436).sum := by decide
  have hdescent : baseEnd_1927436 < baseStart_1927436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927509 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1927509 : Nat := 118140960795 + 1927509 * 2 ^ 59
def prefixEnd_1927509 : Nat := 4983230072969 + 3 ^ 40 * 1927509 * 2
def baseEnd_1927509 : Nat := 659825721911469563915369

theorem tailTrace_1927509 : CollatzResearch.WordTrace tailWord_1927509 prefixEnd_1927509 659825721911469563915369 := by
  unfold tailWord_1927509
  simp only [CollatzResearch.WordTrace]
  refine ⟨70302028773971560173969581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46868019182647706782646387 70302028773971560173969581)
  ·
    refine ⟨26363260790239335065238593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70302028773971560173969581 26363260790239335065238593)
    ·
      refine ⟨19772445592679501298928945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26363260790239335065238593 19772445592679501298928945)
      ·
        refine ⟨14829334194509625974196709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19772445592679501298928945 14829334194509625974196709)
        ·
          refine ⟨2780500161470554870161883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14829334194509625974196709 2780500161470554870161883)
          ·
            refine ⟨4170750242205832305242825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780500161470554870161883 4170750242205832305242825)
            ·
              refine ⟨3128062681654374228932119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4170750242205832305242825 3128062681654374228932119)
              ·
                refine ⟨4692094022481561343398179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128062681654374228932119 4692094022481561343398179)
                ·
                  refine ⟨7038141033722342015097269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692094022481561343398179 7038141033722342015097269)
                  ·
                    refine ⟨659825721911469563915369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7038141033722342015097269 659825721911469563915369)
                    ·
                      rfl

theorem cell22_1927509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1927509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927509 prefixEnd_1927509 := by exact prefixLift 1927509
  have htrace : WordTrace (prefixWord ++ tailWord_1927509) baseStart_1927509 baseEnd_1927509 := by
    simpa [prefixWord, tailWord_1927509, baseEnd_1927509] using wordTrace_append hprefix tailTrace_1927509
  have hstable : (prefixWord ++ tailWord_1927509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927509).length < 2 ^ (prefixWord ++ tailWord_1927509).sum := by decide
  have hdescent : baseEnd_1927509 < baseStart_1927509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927535 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_1927535 : Nat := 118140960795 + 1927535 * 2 ^ 59
def prefixEnd_1927535 : Nat := 4983230072969 + 3 ^ 40 * 1927535 * 2
def baseEnd_1927535 : Nat := 659834622242814162765289

theorem tailTrace_1927535 : CollatzResearch.WordTrace tailWord_1927535 prefixEnd_1927535 659834622242814162765289 := by
  unfold tailWord_1927535
  simp only [CollatzResearch.WordTrace]
  refine ⟨70302977071877366614416059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46868651381251577742944039 70302977071877366614416059)
  ·
    refine ⟨105454465607816049921624089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70302977071877366614416059 105454465607816049921624089)
    ·
      refine ⟨79090849205862037441218067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105454465607816049921624089 79090849205862037441218067)
      ·
        refine ⟨118636273808793056161827101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79090849205862037441218067 118636273808793056161827101)
        ·
          refine ⟨44488602678297396060685163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118636273808793056161827101 44488602678297396060685163)
          ·
            refine ⟨66732904017446094091027745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44488602678297396060685163 66732904017446094091027745)
            ·
              refine ⟨50049678013084570568270809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66732904017446094091027745 50049678013084570568270809)
              ·
                refine ⟨37537258509813427926203107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50049678013084570568270809 37537258509813427926203107)
                ·
                  refine ⟨56305887764720141889304661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37537258509813427926203107 56305887764720141889304661)
                  ·
                    refine ⟨659834622242814162765289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56305887764720141889304661 659834622242814162765289)
                    ·
                      rfl

theorem cell22_1927535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_1927535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927535 prefixEnd_1927535 := by exact prefixLift 1927535
  have htrace : WordTrace (prefixWord ++ tailWord_1927535) baseStart_1927535 baseEnd_1927535 := by
    simpa [prefixWord, tailWord_1927535, baseEnd_1927535] using wordTrace_append hprefix tailTrace_1927535
  have hstable : (prefixWord ++ tailWord_1927535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927535).length < 2 ^ (prefixWord ++ tailWord_1927535).sum := by decide
  have hdescent : baseEnd_1927535 < baseStart_1927535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927537 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_1927537 : Nat := 118140960795 + 1927537 * 2 ^ 59
def prefixEnd_1927537 : Nat := 4983230072969 + 3 ^ 40 * 1927537 * 2
def baseEnd_1927537 : Nat := 659835306883686824215283

theorem tailTrace_1927537 : CollatzResearch.WordTrace tailWord_1927537 prefixEnd_1927537 659835306883686824215283 := by
  unfold tailWord_1927537
  simp only [CollatzResearch.WordTrace]
  refine ⟨70303050017870120955988865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46868700011913413970659243 70303050017870120955988865)
  ·
    refine ⟨52727287513402590716991649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70303050017870120955988865 52727287513402590716991649)
    ·
      refine ⟨39545465635051943037743737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52727287513402590716991649 39545465635051943037743737)
      ·
        refine ⟨29659099226288957278307803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39545465635051943037743737 29659099226288957278307803)
        ·
          refine ⟨44488648839433435917461705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29659099226288957278307803 44488648839433435917461705)
          ·
            refine ⟨33366486629575076938096279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44488648839433435917461705 33366486629575076938096279)
            ·
              refine ⟨50049729944362615407144419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33366486629575076938096279 50049729944362615407144419)
              ·
                refine ⟨75074594916543923110716629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50049729944362615407144419 75074594916543923110716629)
                ·
                  refine ⟨1759560818356498197907421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 75074594916543923110716629 1759560818356498197907421)
                  ·
                    refine ⟨659835306883686824215283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759560818356498197907421 659835306883686824215283)
                    ·
                      rfl

theorem cell22_1927537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_1927537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927537 prefixEnd_1927537 := by exact prefixLift 1927537
  have htrace : WordTrace (prefixWord ++ tailWord_1927537) baseStart_1927537 baseEnd_1927537 := by
    simpa [prefixWord, tailWord_1927537, baseEnd_1927537] using wordTrace_append hprefix tailTrace_1927537
  have hstable : (prefixWord ++ tailWord_1927537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927537).length < 2 ^ (prefixWord ++ tailWord_1927537).sum := by decide
  have hdescent : baseEnd_1927537 < baseStart_1927537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927605 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1927605 : Nat := 118140960795 + 1927605 * 2 ^ 59
def prefixEnd_1927605 : Nat := 4983230072969 + 3 ^ 40 * 1927605 * 2
def baseEnd_1927605 : Nat := 659858584673357313515075

theorem tailTrace_1927605 : CollatzResearch.WordTrace tailWord_1927605 prefixEnd_1927605 659858584673357313515075 := by
  unfold tailWord_1927605
  simp only [CollatzResearch.WordTrace]
  refine ⟨70305530181623768569464269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46870353454415845712976179 70305530181623768569464269)
  ·
    refine ⟨26364573818108913213549101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70305530181623768569464269 26364573818108913213549101)
    ·
      refine ⟨9886715181790842455080913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26364573818108913213549101 9886715181790842455080913)
      ·
        refine ⟨7415036386343131841310685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9886715181790842455080913 7415036386343131841310685)
        ·
          refine ⟨2780638644878674440491507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7415036386343131841310685 2780638644878674440491507)
          ·
            refine ⟨4170957967318011660737261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780638644878674440491507 4170957967318011660737261)
            ·
              refine ⟨1564109237744254372776473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4170957967318011660737261 1564109237744254372776473)
              ·
                refine ⟨1173081928308190779582355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564109237744254372776473 1173081928308190779582355)
                ·
                  refine ⟨1759622892462286169373533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173081928308190779582355 1759622892462286169373533)
                  ·
                    refine ⟨659858584673357313515075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759622892462286169373533 659858584673357313515075)
                    ·
                      rfl

theorem cell22_1927605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1927605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927605 prefixEnd_1927605 := by exact prefixLift 1927605
  have htrace : WordTrace (prefixWord ++ tailWord_1927605) baseStart_1927605 baseEnd_1927605 := by
    simpa [prefixWord, tailWord_1927605, baseEnd_1927605] using wordTrace_append hprefix tailTrace_1927605
  have hstable : (prefixWord ++ tailWord_1927605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927605).length < 2 ^ (prefixWord ++ tailWord_1927605).sum := by decide
  have hdescent : baseEnd_1927605 < baseStart_1927605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927627 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 1, 5]
def baseStart_1927627 : Nat := 118140960795 + 1927627 * 2 ^ 59
def prefixEnd_1927627 : Nat := 4983230072969 + 3 ^ 40 * 1927627 * 2
def baseEnd_1927627 : Nat := 659866115722956589465007

theorem tailTrace_1927627 : CollatzResearch.WordTrace tailWord_1927627 prefixEnd_1927627 659866115722956589465007 := by
  unfold tailWord_1927627
  simp only [CollatzResearch.WordTrace]
  refine ⟨70306332587544066326765135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46870888391696044217843423 70306332587544066326765135)
  ·
    refine ⟨105459498881316099490147703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70306332587544066326765135 105459498881316099490147703)
    ·
      refine ⟨158189248321974149235221555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105459498881316099490147703 158189248321974149235221555)
      ·
        refine ⟨237283872482961223852832333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158189248321974149235221555 237283872482961223852832333)
        ·
          refine ⟨88981452181110458944812125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237283872482961223852832333 88981452181110458944812125)
          ·
            refine ⟨33368044567916422104304547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88981452181110458944812125 33368044567916422104304547)
            ·
              refine ⟨50052066851874633156456821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33368044567916422104304547 50052066851874633156456821)
              ·
                refine ⟨4692381267363246858417827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50052066851874633156456821 4692381267363246858417827)
                ·
                  refine ⟨7038571901044870287626741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692381267363246858417827 7038571901044870287626741)
                  ·
                    refine ⟨659866115722956589465007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7038571901044870287626741 659866115722956589465007)
                    ·
                      rfl

theorem cell22_1927627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_1927627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927627 prefixEnd_1927627 := by exact prefixLift 1927627
  have htrace : WordTrace (prefixWord ++ tailWord_1927627) baseStart_1927627 baseEnd_1927627 := by
    simpa [prefixWord, tailWord_1927627, baseEnd_1927627] using wordTrace_append hprefix tailTrace_1927627
  have hstable : (prefixWord ++ tailWord_1927627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927627).length < 2 ^ (prefixWord ++ tailWord_1927627).sum := by decide
  have hdescent : baseEnd_1927627 < baseStart_1927627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927693 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1927693 : Nat := 118140960795 + 1927693 * 2 ^ 59
def prefixEnd_1927693 : Nat := 4983230072969 + 3 ^ 40 * 1927693 * 2
def baseEnd_1927693 : Nat := 659888708871754417314805

theorem tailTrace_1927693 : CollatzResearch.WordTrace tailWord_1927693 prefixEnd_1927693 659888708871754417314805 := by
  unfold tailWord_1927693
  simp only [CollatzResearch.WordTrace]
  refine ⟨70308739805304959598667733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46872493203536639732445155 70308739805304959598667733)
  ·
    refine ⟨1647861089186834990593775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 70308739805304959598667733 1647861089186834990593775)
    ·
      refine ⟨2471791633780252485890663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647861089186834990593775 2471791633780252485890663)
      ·
        refine ⟨3707687450670378728835995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471791633780252485890663 3707687450670378728835995)
        ·
          refine ⟨5561531176005568093253993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707687450670378728835995 5561531176005568093253993)
          ·
            refine ⟨4171148382004176069940495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5561531176005568093253993 4171148382004176069940495)
            ·
              refine ⟨6256722573006264104910743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171148382004176069940495 6256722573006264104910743)
              ·
                refine ⟨9385083859509396157366115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256722573006264104910743 9385083859509396157366115)
                ·
                  refine ⟨14077625789264094236049173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9385083859509396157366115 14077625789264094236049173)
                  ·
                    refine ⟨659888708871754417314805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14077625789264094236049173 659888708871754417314805)
                    ·
                      rfl

theorem cell22_1927693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1927693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927693 prefixEnd_1927693 := by exact prefixLift 1927693
  have htrace : WordTrace (prefixWord ++ tailWord_1927693) baseStart_1927693 baseEnd_1927693 := by
    simpa [prefixWord, tailWord_1927693, baseEnd_1927693] using wordTrace_append hprefix tailTrace_1927693
  have hstable : (prefixWord ++ tailWord_1927693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927693).length < 2 ^ (prefixWord ++ tailWord_1927693).sum := by decide
  have hdescent : baseEnd_1927693 < baseStart_1927693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927736 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 5]
def baseStart_1927736 : Nat := 118140960795 + 1927736 * 2 ^ 59
def prefixEnd_1927736 : Nat := 4983230072969 + 3 ^ 40 * 1927736 * 2
def baseEnd_1927736 : Nat := 219967809550172212829891

theorem tailTrace_1927736 : CollatzResearch.WordTrace tailWord_1927736 prefixEnd_1927736 219967809550172212829891 := by
  unfold tailWord_1927736
  simp only [CollatzResearch.WordTrace]
  refine ⟨35155154072074588971241531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46873538762766118628322041 35155154072074588971241531)
  ·
    refine ⟨52732731108111883456862297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35155154072074588971241531 52732731108111883456862297)
    ·
      refine ⟨39549548331083912592646723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52732731108111883456862297 39549548331083912592646723)
      ·
        refine ⟨59324322496625868888970085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39549548331083912592646723 59324322496625868888970085)
        ·
          refine ⟨11123310468117350416681891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59324322496625868888970085 11123310468117350416681891)
          ·
            refine ⟨16684965702176025625022837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123310468117350416681891 16684965702176025625022837)
            ·
              refine ⟨1564215534579002402345891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16684965702176025625022837 1564215534579002402345891)
              ·
                refine ⟨2346323301868503603518837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564215534579002402345891 2346323301868503603518837)
                ·
                  refine ⟨219967809550172212829891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346323301868503603518837 219967809550172212829891)
                  ·
                    rfl

theorem cell22_1927736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_1927736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927736 prefixEnd_1927736 := by exact prefixLift 1927736
  have htrace : WordTrace (prefixWord ++ tailWord_1927736) baseStart_1927736 baseEnd_1927736 := by
    simpa [prefixWord, tailWord_1927736, baseEnd_1927736] using wordTrace_append hprefix tailTrace_1927736
  have hstable : (prefixWord ++ tailWord_1927736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927736).length < 2 ^ (prefixWord ++ tailWord_1927736).sum := by decide
  have hdescent : baseEnd_1927736 < baseStart_1927736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927757 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1927757 : Nat := 118140960795 + 1927757 * 2 ^ 59
def prefixEnd_1927757 : Nat := 4983230072969 + 3 ^ 40 * 1927757 * 2
def baseEnd_1927757 : Nat := 659910617379679583714609

theorem tailTrace_1927757 : CollatzResearch.WordTrace tailWord_1927757 prefixEnd_1927757 659910617379679583714609 := by
  unfold tailWord_1927757
  simp only [CollatzResearch.WordTrace]
  refine ⟨70311074077073098528997525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46874049384715399019331683 70311074077073098528997525)
  ·
    refine ⟨3295831597362801493546759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70311074077073098528997525 3295831597362801493546759)
    ·
      refine ⟨4943747396044202240320139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3295831597362801493546759 4943747396044202240320139)
      ·
        refine ⟨7415621094066303360480209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4943747396044202240320139 7415621094066303360480209)
        ·
          refine ⟨5561715820549727520360157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7415621094066303360480209 5561715820549727520360157)
          ·
            refine ⟨2085643432706147820135059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5561715820549727520360157 2085643432706147820135059)
            ·
              refine ⟨3128465149059221730202589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085643432706147820135059 3128465149059221730202589)
              ·
                refine ⟨1173174430897208148825971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3128465149059221730202589 1173174430897208148825971)
                ·
                  refine ⟨1759761646345812223238957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173174430897208148825971 1759761646345812223238957)
                  ·
                    refine ⟨659910617379679583714609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759761646345812223238957 659910617379679583714609)
                    ·
                      rfl

theorem cell22_1927757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1927757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927757 prefixEnd_1927757 := by exact prefixLift 1927757
  have htrace : WordTrace (prefixWord ++ tailWord_1927757) baseStart_1927757 baseEnd_1927757 := by
    simpa [prefixWord, tailWord_1927757, baseEnd_1927757] using wordTrace_append hprefix tailTrace_1927757
  have hstable : (prefixWord ++ tailWord_1927757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927757).length < 2 ^ (prefixWord ++ tailWord_1927757).sum := by decide
  have hdescent : baseEnd_1927757 < baseStart_1927757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927774 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1927774 : Nat := 118140960795 + 1927774 * 2 ^ 59
def prefixEnd_1927774 : Nat := 4983230072969 + 3 ^ 40 * 1927774 * 2
def baseEnd_1927774 : Nat := 659916436827097206039557

theorem tailTrace_1927774 : CollatzResearch.WordTrace tailWord_1927774 prefixEnd_1927774 659916436827097206039557 := by
  unfold tailWord_1927774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788961764751438804045797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46874462745341006954910917 8788961764751438804045797)
  ·
    refine ⟨1647930330890894775758587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8788961764751438804045797 1647930330890894775758587)
    ·
      refine ⟨2471895496336342163637881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647930330890894775758587 2471895496336342163637881)
      ·
        refine ⟨1853921622252256622728411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2471895496336342163637881 1853921622252256622728411)
        ·
          refine ⟨2780882433378384934092617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853921622252256622728411 2780882433378384934092617)
          ·
            refine ⟨2085661825033788700569463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780882433378384934092617 2085661825033788700569463)
            ·
              refine ⟨3128492737550683050854195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085661825033788700569463 3128492737550683050854195)
              ·
                refine ⟨4692739106326024576281293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128492737550683050854195 4692739106326024576281293)
                ·
                  refine ⟨1759777164872259216105485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4692739106326024576281293 1759777164872259216105485)
                  ·
                    refine ⟨659916436827097206039557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759777164872259216105485 659916436827097206039557)
                    ·
                      rfl

theorem cell22_1927774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1927774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927774 prefixEnd_1927774 := by exact prefixLift 1927774
  have htrace : WordTrace (prefixWord ++ tailWord_1927774) baseStart_1927774 baseEnd_1927774 := by
    simpa [prefixWord, tailWord_1927774, baseEnd_1927774] using wordTrace_append hprefix tailTrace_1927774
  have hstable : (prefixWord ++ tailWord_1927774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927774).length < 2 ^ (prefixWord ++ tailWord_1927774).sum := by decide
  have hdescent : baseEnd_1927774 < baseStart_1927774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927809 : List Nat := [1, 2, 4, 2, 1, 1, 1, 10]
def baseStart_1927809 : Nat := 118140960795 + 1927809 * 2 ^ 59
def prefixEnd_1927809 : Nat := 4983230072969 + 3 ^ 40 * 1927809 * 2
def baseEnd_1927809 : Nat := 73325379782485420157161

theorem tailTrace_1927809 : CollatzResearch.WordTrace tailWord_1927809 prefixEnd_1927809 73325379782485420157161 := by
  unfold tailWord_1927809
  simp only [CollatzResearch.WordTrace]
  refine ⟨70312970672884711409890481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46875313781923140939926987 70312970672884711409890481)
  ·
    refine ⟨52734728004663533557417861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70312970672884711409890481 52734728004663533557417861)
    ·
      refine ⟨9887761500874412542015849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52734728004663533557417861 9887761500874412542015849)
      ·
        refine ⟨7415821125655809406511887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9887761500874412542015849 7415821125655809406511887)
        ·
          refine ⟨11123731688483714109767831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415821125655809406511887 11123731688483714109767831)
          ·
            refine ⟨16685597532725571164651747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123731688483714109767831 16685597532725571164651747)
            ·
              refine ⟨25028396299088356746977621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16685597532725571164651747 25028396299088356746977621)
              ·
                refine ⟨73325379782485420157161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25028396299088356746977621 73325379782485420157161)
                ·
                  rfl

theorem cell22_1927809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 10].length) (baseStart_1927809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927809 prefixEnd_1927809 := by exact prefixLift 1927809
  have htrace : WordTrace (prefixWord ++ tailWord_1927809) baseStart_1927809 baseEnd_1927809 := by
    simpa [prefixWord, tailWord_1927809, baseEnd_1927809] using wordTrace_append hprefix tailTrace_1927809
  have hstable : (prefixWord ++ tailWord_1927809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927809).length < 2 ^ (prefixWord ++ tailWord_1927809).sum := by decide
  have hdescent : baseEnd_1927809 < baseStart_1927809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927828 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1927828 : Nat := 118140960795 + 1927828 * 2 ^ 59
def prefixEnd_1927828 : Nat := 4983230072969 + 3 ^ 40 * 1927828 * 2
def baseEnd_1927828 : Nat := 659934922130659065189391

theorem tailTrace_1927828 : CollatzResearch.WordTrace tailWord_1927828 prefixEnd_1927828 659934922130659065189391 := by
  unfold tailWord_1927828
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156831829907938827416069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46875775773210585103221425 35156831829907938827416069)
  ·
    refine ⟨6591905968107738530140513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35156831829907938827416069 6591905968107738530140513)
    ·
      refine ⟨4943929476080803897605385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6591905968107738530140513 4943929476080803897605385)
      ·
        refine ⟨3707947107060602923204039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4943929476080803897605385 3707947107060602923204039)
        ·
          refine ⟨5561920660590904384806059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707947107060602923204039 5561920660590904384806059)
          ·
            refine ⟨8342880990886356577209089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561920660590904384806059 8342880990886356577209089)
            ·
              refine ⟨6257160743164767432906817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8342880990886356577209089 6257160743164767432906817)
              ·
                refine ⟨4692870557373575574680113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257160743164767432906817 4692870557373575574680113)
                ·
                  refine ⟨3519652918030181681010085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4692870557373575574680113 3519652918030181681010085)
                  ·
                    refine ⟨659934922130659065189391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3519652918030181681010085 659934922130659065189391)
                    ·
                      rfl

theorem cell22_1927828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1927828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927828 prefixEnd_1927828 := by exact prefixLift 1927828
  have htrace : WordTrace (prefixWord ++ tailWord_1927828) baseStart_1927828 baseEnd_1927828 := by
    simpa [prefixWord, tailWord_1927828, baseEnd_1927828] using wordTrace_append hprefix tailTrace_1927828
  have hstable : (prefixWord ++ tailWord_1927828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927828).length < 2 ^ (prefixWord ++ tailWord_1927828).sum := by decide
  have hdescent : baseEnd_1927828 < baseStart_1927828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927862 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1927862 : Nat := 118140960795 + 1927862 * 2 ^ 59
def prefixEnd_1927862 : Nat := 4983230072969 + 3 ^ 40 * 1927862 * 2
def baseEnd_1927862 : Nat := 659946561025494309839287

theorem tailTrace_1927862 : CollatzResearch.WordTrace tailWord_1927862 prefixEnd_1927862 659946561025494309839287 := by
  unfold tailWord_1927862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394681483855793841348115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46876602494461800974379893 4394681483855793841348115)
  ·
    refine ⟨6592022225783690762022173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394681483855793841348115 6592022225783690762022173)
    ·
      refine ⟨2472008334668884035758315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6592022225783690762022173 2472008334668884035758315)
      ·
        refine ⟨3708012502003326053637473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472008334668884035758315 3708012502003326053637473)
        ·
          refine ⟨2781009376502494540228105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3708012502003326053637473 2781009376502494540228105)
          ·
            refine ⟨2085757032376870905171079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781009376502494540228105 2085757032376870905171079)
            ·
              refine ⟨3128635548565306357756619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085757032376870905171079 3128635548565306357756619)
              ·
                refine ⟨4692953322847959536634929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128635548565306357756619 4692953322847959536634929)
                ·
                  refine ⟨3519714992135969652476197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4692953322847959536634929 3519714992135969652476197)
                  ·
                    refine ⟨659946561025494309839287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3519714992135969652476197 659946561025494309839287)
                    ·
                      rfl

theorem cell22_1927862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1927862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927862 prefixEnd_1927862 := by exact prefixLift 1927862
  have htrace : WordTrace (prefixWord ++ tailWord_1927862) baseStart_1927862 baseEnd_1927862 := by
    simpa [prefixWord, tailWord_1927862, baseEnd_1927862] using wordTrace_append hprefix tailTrace_1927862
  have hstable : (prefixWord ++ tailWord_1927862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927862).length < 2 ^ (prefixWord ++ tailWord_1927862).sum := by decide
  have hdescent : baseEnd_1927862 < baseStart_1927862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927886 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1927886 : Nat := 118140960795 + 1927886 * 2 ^ 59
def prefixEnd_1927886 : Nat := 4983230072969 + 3 ^ 40 * 1927886 * 2
def baseEnd_1927886 : Nat := 659954776715966247239213

theorem tailTrace_1927886 : CollatzResearch.WordTrace tailWord_1927886 prefixEnd_1927886 659954776715966247239213 := by
  unfold tailWord_1927886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789472386700719195055439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46877186062403835706962341 8789472386700719195055439)
  ·
    refine ⟨13184208580051078792583159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8789472386700719195055439 13184208580051078792583159)
    ·
      refine ⟨19776312870076618188874739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13184208580051078792583159 19776312870076618188874739)
      ·
        refine ⟨29664469305114927283312109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19776312870076618188874739 29664469305114927283312109)
        ·
          refine ⟨11124175989418097731242041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29664469305114927283312109 11124175989418097731242041)
          ·
            refine ⟨8343131992063573298431531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11124175989418097731242041 8343131992063573298431531)
            ·
              refine ⟨12514697988095359947647297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343131992063573298431531 12514697988095359947647297)
              ·
                refine ⟨9386023491071519960735473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12514697988095359947647297 9386023491071519960735473)
                ·
                  refine ⟨7039517618303639970551605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9386023491071519960735473 7039517618303639970551605)
                  ·
                    refine ⟨659954776715966247239213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7039517618303639970551605 659954776715966247239213)
                    ·
                      rfl

theorem cell22_1927886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1927886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927886 prefixEnd_1927886 := by exact prefixLift 1927886
  have htrace : WordTrace (prefixWord ++ tailWord_1927886) baseStart_1927886 baseEnd_1927886 := by
    simpa [prefixWord, tailWord_1927886, baseEnd_1927886] using wordTrace_append hprefix tailTrace_1927886
  have hstable : (prefixWord ++ tailWord_1927886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927886).length < 2 ^ (prefixWord ++ tailWord_1927886).sum := by decide
  have hdescent : baseEnd_1927886 < baseStart_1927886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927918 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1927918 : Nat := 118140960795 + 1927918 * 2 ^ 59
def prefixEnd_1927918 : Nat := 4983230072969 + 3 ^ 40 * 1927918 * 2
def baseEnd_1927918 : Nat := 659965730969928830439115

theorem tailTrace_1927918 : CollatzResearch.WordTrace tailWord_1927918 prefixEnd_1927918 659965730969928830439115 := by
  unfold tailWord_1927918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789618278686227878201051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46877964152993215350405605 8789618278686227878201051)
  ·
    refine ⟨13184427418029341817301577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8789618278686227878201051 13184427418029341817301577)
    ·
      refine ⟨9888320563522006362976183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13184427418029341817301577 9888320563522006362976183)
      ·
        refine ⟨14832480845283009544464275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9888320563522006362976183 14832480845283009544464275)
        ·
          refine ⟨22248721267924514316696413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832480845283009544464275 22248721267924514316696413)
          ·
            refine ⟨8343270475471692868761155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22248721267924514316696413 8343270475471692868761155)
            ·
              refine ⟨12514905713207539303141733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343270475471692868761155 12514905713207539303141733)
              ·
                refine ⟨2346544821226413619339075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12514905713207539303141733 2346544821226413619339075)
                ·
                  refine ⟨3519817231839620429008613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346544821226413619339075 3519817231839620429008613)
                  ·
                    refine ⟨659965730969928830439115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3519817231839620429008613 659965730969928830439115)
                    ·
                      rfl

theorem cell22_1927918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1927918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927918 prefixEnd_1927918 := by exact prefixLift 1927918
  have htrace : WordTrace (prefixWord ++ tailWord_1927918) baseStart_1927918 baseEnd_1927918 := by
    simpa [prefixWord, tailWord_1927918, baseEnd_1927918] using wordTrace_append hprefix tailTrace_1927918
  have hstable : (prefixWord ++ tailWord_1927918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927918).length < 2 ^ (prefixWord ++ tailWord_1927918).sum := by decide
  have hdescent : baseEnd_1927918 < baseStart_1927918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927948 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_1927948 : Nat := 118140960795 + 1927948 * 2 ^ 59
def prefixEnd_1927948 : Nat := 4983230072969 + 3 ^ 40 * 1927948 * 2
def baseEnd_1927948 : Nat := 659976000583018752189023

theorem tailTrace_1927948 : CollatzResearch.WordTrace tailWord_1927948 prefixEnd_1927948 659976000583018752189023 := by
  unfold tailWord_1927948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35159020209690569074600249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46878693612920758766133665 35159020209690569074600249)
  ·
    refine ⟨26369265157267926805950187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35159020209690569074600249 26369265157267926805950187)
    ·
      refine ⟨39553897735901890208925281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26369265157267926805950187 39553897735901890208925281)
      ·
        refine ⟨29665423301926417656693961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39553897735901890208925281 29665423301926417656693961)
        ·
          refine ⟨22249067476444813242520471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29665423301926417656693961 22249067476444813242520471)
          ·
            refine ⟨33373601214667219863780707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22249067476444813242520471 33373601214667219863780707)
            ·
              refine ⟨50060401822000829795671061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33373601214667219863780707 50060401822000829795671061)
              ·
                refine ⟨2346581335406288896672081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50060401822000829795671061 2346581335406288896672081)
                ·
                  refine ⟨1759936001554716672504061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2346581335406288896672081 1759936001554716672504061)
                  ·
                    refine ⟨659976000583018752189023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759936001554716672504061 659976000583018752189023)
                    ·
                      rfl

theorem cell22_1927948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_1927948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1927948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1927948 prefixEnd_1927948 := by exact prefixLift 1927948
  have htrace : WordTrace (prefixWord ++ tailWord_1927948) baseStart_1927948 baseEnd_1927948 := by
    simpa [prefixWord, tailWord_1927948, baseEnd_1927948] using wordTrace_append hprefix tailTrace_1927948
  have hstable : (prefixWord ++ tailWord_1927948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927948).length < 2 ^ (prefixWord ++ tailWord_1927948).sum := by decide
  have hdescent : baseEnd_1927948 < baseStart_1927948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928001 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 4]
def baseStart_1928001 : Nat := 118140960795 + 1928001 * 2 ^ 59
def prefixEnd_1928001 : Nat := 4983230072969 + 3 ^ 40 * 1928001 * 2
def baseEnd_1928001 : Nat := 219998047855381426871287

theorem tailTrace_1928001 : CollatzResearch.WordTrace tailWord_1928001 prefixEnd_1928001 219998047855381426871287 := by
  unfold tailWord_1928001
  simp only [CollatzResearch.WordTrace]
  refine ⟨70319973488189128200879857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46879982325459418800586571 70319973488189128200879857)
  ·
    refine ⟨52739980116141846150659893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70319973488189128200879857 52739980116141846150659893)
    ·
      refine ⟨4944373135888298076624365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52739980116141846150659893 4944373135888298076624365)
      ·
        refine ⟨1854139925958111778734137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4944373135888298076624365 1854139925958111778734137)
        ·
          refine ⟨1390604944468583834050603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1854139925958111778734137 1390604944468583834050603)
          ·
            refine ⟨2085907416702875751075905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390604944468583834050603 2085907416702875751075905)
            ·
              refine ⟨1564430562527156813306929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085907416702875751075905 1564430562527156813306929)
              ·
                refine ⟨1173322921895367609980197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564430562527156813306929 1173322921895367609980197)
                ·
                  refine ⟨219998047855381426871287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173322921895367609980197 219998047855381426871287)
                  ·
                    rfl

theorem cell22_1928001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_1928001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928001 prefixEnd_1928001 := by exact prefixLift 1928001
  have htrace : WordTrace (prefixWord ++ tailWord_1928001) baseStart_1928001 baseEnd_1928001 := by
    simpa [prefixWord, tailWord_1928001, baseEnd_1928001] using wordTrace_append hprefix tailTrace_1928001
  have hstable : (prefixWord ++ tailWord_1928001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928001).length < 2 ^ (prefixWord ++ tailWord_1928001).sum := by decide
  have hdescent : baseEnd_1928001 < baseStart_1928001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928023 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 5]
def baseStart_1928023 : Nat := 118140960795 + 1928023 * 2 ^ 59
def prefixEnd_1928023 : Nat := 4983230072969 + 3 ^ 40 * 1928023 * 2
def baseEnd_1928023 : Nat := 220000558205247852187931

theorem tailTrace_1928023 : CollatzResearch.WordTrace tailWord_1928023 prefixEnd_1928023 220000558205247852187931 := by
  unfold tailWord_1928023
  simp only [CollatzResearch.WordTrace]
  refine ⟨70320775894109425958180723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46880517262739617305453815 70320775894109425958180723)
  ·
    refine ⟨105481163841164138937271085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70320775894109425958180723 105481163841164138937271085)
    ·
      refine ⟨39555436440436552101476657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105481163841164138937271085 39555436440436552101476657)
      ·
        refine ⟨29666577330327414076107493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39555436440436552101476657 29666577330327414076107493)
        ·
          refine ⟨5562483249436390139270155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29666577330327414076107493 5562483249436390139270155)
          ·
            refine ⟨8343724874154585208905233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562483249436390139270155 8343724874154585208905233)
            ·
              refine ⟨6257793655615938906678925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8343724874154585208905233 6257793655615938906678925)
              ·
                refine ⟨2346672620855977090004597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6257793655615938906678925 2346672620855977090004597)
                ·
                  refine ⟨220000558205247852187931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346672620855977090004597 220000558205247852187931)
                  ·
                    rfl

theorem cell22_1928023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 5].length) (baseStart_1928023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928023 prefixEnd_1928023 := by exact prefixLift 1928023
  have htrace : WordTrace (prefixWord ++ tailWord_1928023) baseStart_1928023 baseEnd_1928023 := by
    simpa [prefixWord, tailWord_1928023, baseEnd_1928023] using wordTrace_append hprefix tailTrace_1928023
  have hstable : (prefixWord ++ tailWord_1928023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928023).length < 2 ^ (prefixWord ++ tailWord_1928023).sum := by decide
  have hdescent : baseEnd_1928023 < baseStart_1928023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928175 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 5]
def baseStart_1928175 : Nat := 118140960795 + 1928175 * 2 ^ 59
def prefixEnd_1928175 : Nat := 4983230072969 + 3 ^ 40 * 1928175 * 2
def baseEnd_1928175 : Nat := 220017902440688608921109

theorem tailTrace_1928175 : CollatzResearch.WordTrace tailWord_1928175 prefixEnd_1928175 220017902440688608921109 := by
  unfold tailWord_1928175
  simp only [CollatzResearch.WordTrace]
  refine ⟨70326319789558755917713979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46884213193039170611809319 70326319789558755917713979)
  ·
    refine ⟨105489479684338133876570969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70326319789558755917713979 105489479684338133876570969)
    ·
      refine ⟨79117109763253600407428227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105489479684338133876570969 79117109763253600407428227)
      ·
        refine ⟨118675664644880400611142341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79117109763253600407428227 118675664644880400611142341)
        ·
          refine ⟨22251687120915075114589189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118675664644880400611142341 22251687120915075114589189)
          ·
            refine ⟨4172191335171576583985473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22251687120915075114589189 4172191335171576583985473)
            ·
              refine ⟨3129143501378682437989105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172191335171576583985473 3129143501378682437989105)
              ·
                refine ⟨2346857626034011828491829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3129143501378682437989105 2346857626034011828491829)
                ·
                  refine ⟨220017902440688608921109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346857626034011828491829 220017902440688608921109)
                  ·
                    rfl

theorem cell22_1928175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 5].length) (baseStart_1928175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928175 prefixEnd_1928175 := by exact prefixLift 1928175
  have htrace : WordTrace (prefixWord ++ tailWord_1928175) baseStart_1928175 baseEnd_1928175 := by
    simpa [prefixWord, tailWord_1928175, baseEnd_1928175] using wordTrace_append hprefix tailTrace_1928175
  have hstable : (prefixWord ++ tailWord_1928175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928175).length < 2 ^ (prefixWord ++ tailWord_1928175).sum := by decide
  have hdescent : baseEnd_1928175 < baseStart_1928175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928203 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 8]
def baseStart_1928203 : Nat := 118140960795 + 1928203 * 2 ^ 59
def prefixEnd_1928203 : Nat := 4983230072969 + 3 ^ 40 * 1928203 * 2
def baseEnd_1928203 : Nat := 220021097431427695687747

theorem tailTrace_1928203 : CollatzResearch.WordTrace tailWord_1928203 prefixEnd_1928203 220021097431427695687747 := by
  unfold tailWord_1928203
  simp only [CollatzResearch.WordTrace]
  refine ⟨70327341033457316699733263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46884894022304877799822175 70327341033457316699733263)
  ·
    refine ⟨105491011550185975049599895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70327341033457316699733263 105491011550185975049599895)
    ·
      refine ⟨158236517325278962574399843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105491011550185975049599895 158236517325278962574399843)
      ·
        refine ⟨237354775987918443861599765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158236517325278962574399843 237354775987918443861599765)
        ·
          refine ⟨11126005124433677056012489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237354775987918443861599765 11126005124433677056012489)
          ·
            refine ⟨8344503843325257792009367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11126005124433677056012489 8344503843325257792009367)
            ·
              refine ⟨12516755764987886688014051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344503843325257792009367 12516755764987886688014051)
              ·
                refine ⟨18775133647481830032021077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12516755764987886688014051 18775133647481830032021077)
                ·
                  refine ⟨220021097431427695687747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18775133647481830032021077 220021097431427695687747)
                  ·
                    rfl

theorem cell22_1928203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_1928203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928203 prefixEnd_1928203 := by exact prefixLift 1928203
  have htrace : WordTrace (prefixWord ++ tailWord_1928203) baseStart_1928203 baseEnd_1928203 := by
    simpa [prefixWord, tailWord_1928203, baseEnd_1928203] using wordTrace_append hprefix tailTrace_1928203
  have hstable : (prefixWord ++ tailWord_1928203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928203).length < 2 ^ (prefixWord ++ tailWord_1928203).sum := by decide
  have hdescent : baseEnd_1928203 < baseStart_1928203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928235 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 4, 3]
def baseStart_1928235 : Nat := 118140960795 + 1928235 * 2 ^ 59
def prefixEnd_1928235 : Nat := 4983230072969 + 3 ^ 40 * 1928235 * 2
def baseEnd_1928235 : Nat := 660074246548245670263143

theorem tailTrace_1928235 : CollatzResearch.WordTrace tailWord_1928235 prefixEnd_1928235 660074246548245670263143 := by
  unfold tailWord_1928235
  simp only [CollatzResearch.WordTrace]
  refine ⟨70328508169341386164898159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46885672112894257443265439 70328508169341386164898159)
  ·
    refine ⟨105492762254012079247347239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70328508169341386164898159 105492762254012079247347239)
    ·
      refine ⟨158239143381018118871020859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105492762254012079247347239 158239143381018118871020859)
      ·
        refine ⟨237358715071527178306531289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158239143381018118871020859 237358715071527178306531289)
        ·
          refine ⟨178019036303645383729898467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237358715071527178306531289 178019036303645383729898467)
          ·
            refine ⟨267028554455468075594847701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178019036303645383729898467 267028554455468075594847701)
            ·
              refine ⟨6258481745050033021754243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267028554455468075594847701 6258481745050033021754243)
              ·
                refine ⟨9387722617575049532631365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258481745050033021754243 9387722617575049532631365)
                ·
                  refine ⟨1760197990795321787368381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9387722617575049532631365 1760197990795321787368381)
                  ·
                    refine ⟨660074246548245670263143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760197990795321787368381 660074246548245670263143)
                    ·
                      rfl

theorem cell22_1928235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 3].length) (baseStart_1928235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928235 prefixEnd_1928235 := by exact prefixLift 1928235
  have htrace : WordTrace (prefixWord ++ tailWord_1928235) baseStart_1928235 baseEnd_1928235 := by
    simpa [prefixWord, tailWord_1928235, baseEnd_1928235] using wordTrace_append hprefix tailTrace_1928235
  have hstable : (prefixWord ++ tailWord_1928235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928235).length < 2 ^ (prefixWord ++ tailWord_1928235).sum := by decide
  have hdescent : baseEnd_1928235 < baseStart_1928235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928252 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_1928252 : Nat := 118140960795 + 1928252 * 2 ^ 59
def prefixEnd_1928252 : Nat := 4983230072969 + 3 ^ 40 * 1928252 * 2
def baseEnd_1928252 : Nat := 660080065995663292588091

theorem tailTrace_1928252 : CollatzResearch.WordTrace tailWord_1928252 prefixEnd_1928252 660080065995663292588091 := by
  unfold tailWord_1928252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35164564105139899034133505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46886085473519865378844673 35164564105139899034133505)
  ·
    refine ⟨26373423078854924275600129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35164564105139899034133505 26373423078854924275600129)
    ·
      refine ⟨19780067309141193206700097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26373423078854924275600129 19780067309141193206700097)
      ·
        refine ⟨14835050481855894905025073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19780067309141193206700097 14835050481855894905025073)
        ·
          refine ⟨11126287861391921178768805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14835050481855894905025073 11126287861391921178768805)
          ·
            refine ⟨2086178974010985221019151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11126287861391921178768805 2086178974010985221019151)
            ·
              refine ⟨3129268461016477831528727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086178974010985221019151 3129268461016477831528727)
              ·
                refine ⟨4693902691524716747293091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129268461016477831528727 4693902691524716747293091)
                ·
                  refine ⟨7040854037287075120939637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693902691524716747293091 7040854037287075120939637)
                  ·
                    refine ⟨660080065995663292588091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7040854037287075120939637 660080065995663292588091)
                    ·
                      rfl

theorem cell22_1928252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_1928252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928252 prefixEnd_1928252 := by exact prefixLift 1928252
  have htrace : WordTrace (prefixWord ++ tailWord_1928252) baseStart_1928252 baseEnd_1928252 := by
    simpa [prefixWord, tailWord_1928252, baseEnd_1928252] using wordTrace_append hprefix tailTrace_1928252
  have hstable : (prefixWord ++ tailWord_1928252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928252).length < 2 ^ (prefixWord ++ tailWord_1928252).sum := by decide
  have hdescent : baseEnd_1928252 < baseStart_1928252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928286 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1928286 : Nat := 118140960795 + 1928286 * 2 ^ 59
def prefixEnd_1928286 : Nat := 4983230072969 + 3 ^ 40 * 1928286 * 2
def baseEnd_1928286 : Nat := 660091704890498537237987

theorem tailTrace_1928286 : CollatzResearch.WordTrace tailWord_1928286 prefixEnd_1928286 660091704890498537237987 := by
  unfold tailWord_1928286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791296036519577734375589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46886912194771081250003141 8791296036519577734375589)
  ·
    refine ⟨1648368006847420825195423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8791296036519577734375589 1648368006847420825195423)
    ·
      refine ⟨2472552010271131237793135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648368006847420825195423 2472552010271131237793135)
      ·
        refine ⟨3708828015406696856689703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472552010271131237793135 3708828015406696856689703)
        ·
          refine ⟨5563242023110045285034555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708828015406696856689703 5563242023110045285034555)
          ·
            refine ⟨8344863034665067927551833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563242023110045285034555 8344863034665067927551833)
            ·
              refine ⟨6258647275998800945663875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344863034665067927551833 6258647275998800945663875)
              ·
                refine ⟨9387970913998201418495813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258647275998800945663875 9387970913998201418495813)
                ·
                  refine ⟨1760244546374662765967965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9387970913998201418495813 1760244546374662765967965)
                  ·
                    refine ⟨660091704890498537237987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760244546374662765967965 660091704890498537237987)
                    ·
                      rfl

theorem cell22_1928286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1928286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928286 prefixEnd_1928286 := by exact prefixLift 1928286
  have htrace : WordTrace (prefixWord ++ tailWord_1928286) baseStart_1928286 baseEnd_1928286 := by
    simpa [prefixWord, tailWord_1928286, baseEnd_1928286] using wordTrace_append hprefix tailTrace_1928286
  have hstable : (prefixWord ++ tailWord_1928286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928286).length < 2 ^ (prefixWord ++ tailWord_1928286).sum := by decide
  have hdescent : baseEnd_1928286 < baseStart_1928286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928297 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_1928297 : Nat := 118140960795 + 1928297 * 2 ^ 59
def prefixEnd_1928297 : Nat := 4983230072969 + 3 ^ 40 * 1928297 * 2
def baseEnd_1928297 : Nat := 660095470415298175212953

theorem tailTrace_1928297 : CollatzResearch.WordTrace tailWord_1928297 prefixEnd_1928297 660095470415298175212953 := by
  unfold tailWord_1928297
  simp only [CollatzResearch.WordTrace]
  refine ⟨70330769495116770753655145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46887179663411180502436763 70330769495116770753655145)
  ·
    refine ⟨52748077121337578065241359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70330769495116770753655145 52748077121337578065241359)
    ·
      refine ⟨79122115682006367097862039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52748077121337578065241359 79122115682006367097862039)
      ·
        refine ⟨118683173523009550646793059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79122115682006367097862039 118683173523009550646793059)
        ·
          refine ⟨178024760284514325970189589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118683173523009550646793059 178024760284514325970189589)
          ·
            refine ⟨8344910638336609029852637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178024760284514325970189589 8344910638336609029852637)
            ·
              refine ⟨3129341489376228386194739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8344910638336609029852637 3129341489376228386194739)
              ·
                refine ⟨4694012234064342579292109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129341489376228386194739 4694012234064342579292109)
                ·
                  refine ⟨1760254587774128467234541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4694012234064342579292109 1760254587774128467234541)
                  ·
                    refine ⟨660095470415298175212953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760254587774128467234541 660095470415298175212953)
                    ·
                      rfl

theorem cell22_1928297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_1928297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928297 prefixEnd_1928297 := by exact prefixLift 1928297
  have htrace : WordTrace (prefixWord ++ tailWord_1928297) baseStart_1928297 baseEnd_1928297 := by
    simpa [prefixWord, tailWord_1928297, baseEnd_1928297] using wordTrace_append hprefix tailTrace_1928297
  have hstable : (prefixWord ++ tailWord_1928297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928297).length < 2 ^ (prefixWord ++ tailWord_1928297).sum := by decide
  have hdescent : baseEnd_1928297 < baseStart_1928297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928318 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1928318 : Nat := 118140960795 + 1928318 * 2 ^ 59
def prefixEnd_1928318 : Nat := 4983230072969 + 3 ^ 40 * 1928318 * 2
def baseEnd_1928318 : Nat := 660102659144461120437889

theorem tailTrace_1928318 : CollatzResearch.WordTrace tailWord_1928318 prefixEnd_1928318 660102659144461120437889 := by
  unfold tailWord_1928318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791441928505086417521201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46887690285360460893446405 8791441928505086417521201)
  ·
    refine ⟨6593581446378814813140901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8791441928505086417521201 6593581446378814813140901)
    ·
      refine ⟨1236296521196027777463919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6593581446378814813140901 1236296521196027777463919)
      ·
        refine ⟨1854444781794041666195879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236296521196027777463919 1854444781794041666195879)
        ·
          refine ⟨2781667172691062499293819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854444781794041666195879 2781667172691062499293819)
          ·
            refine ⟨4172500759036593748940729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781667172691062499293819 4172500759036593748940729)
            ·
              refine ⟨3129375569277445311705547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172500759036593748940729 3129375569277445311705547)
              ·
                refine ⟨4694063353916167967558321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129375569277445311705547 4694063353916167967558321)
                ·
                  refine ⟨3520547515437125975668741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4694063353916167967558321 3520547515437125975668741)
                  ·
                    refine ⟨660102659144461120437889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3520547515437125975668741 660102659144461120437889)
                    ·
                      rfl

theorem cell22_1928318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1928318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928318 prefixEnd_1928318 := by exact prefixLift 1928318
  have htrace : WordTrace (prefixWord ++ tailWord_1928318) baseStart_1928318 baseEnd_1928318 := by
    simpa [prefixWord, tailWord_1928318, baseEnd_1928318] using wordTrace_append hprefix tailTrace_1928318
  have hstable : (prefixWord ++ tailWord_1928318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928318).length < 2 ^ (prefixWord ++ tailWord_1928318).sum := by decide
  have hdescent : baseEnd_1928318 < baseStart_1928318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928348 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1928348 : Nat := 118140960795 + 1928348 * 2 ^ 59
def prefixEnd_1928348 : Nat := 4983230072969 + 3 ^ 40 * 1928348 * 2
def baseEnd_1928348 : Nat := 660112928757551042187797

theorem tailTrace_1928348 : CollatzResearch.WordTrace tailWord_1928348 prefixEnd_1928348 660112928757551042187797 := by
  unfold tailWord_1928348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35166314808966003231880849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46888419745288004309174465 35166314808966003231880849)
  ·
    refine ⟨26374736106724502423910637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35166314808966003231880849 26374736106724502423910637)
    ·
      refine ⟨9890526040021688408966489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26374736106724502423910637 9890526040021688408966489)
      ·
        refine ⟨7417894530016266306724867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9890526040021688408966489 7417894530016266306724867)
        ·
          refine ⟨11126841795024399460087301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417894530016266306724867 11126841795024399460087301)
          ·
            refine ⟨2086282836567074898766369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11126841795024399460087301 2086282836567074898766369)
            ·
              refine ⟨1564712127425306174074777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086282836567074898766369 1564712127425306174074777)
              ·
                refine ⟨1173534095568979630556083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564712127425306174074777 1173534095568979630556083)
                ·
                  refine ⟨1760301143353469445834125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173534095568979630556083 1760301143353469445834125)
                  ·
                    refine ⟨660112928757551042187797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760301143353469445834125 660112928757551042187797)
                    ·
                      rfl

theorem cell22_1928348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1928348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928348 prefixEnd_1928348 := by exact prefixLift 1928348
  have htrace : WordTrace (prefixWord ++ tailWord_1928348) baseStart_1928348 baseEnd_1928348 := by
    simpa [prefixWord, tailWord_1928348, baseEnd_1928348] using wordTrace_append hprefix tailTrace_1928348
  have hstable : (prefixWord ++ tailWord_1928348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928348).length < 2 ^ (prefixWord ++ tailWord_1928348).sum := by decide
  have hdescent : baseEnd_1928348 < baseStart_1928348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928402 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1928402 : Nat := 118140960795 + 1928402 * 2 ^ 59
def prefixEnd_1928402 : Nat := 4983230072969 + 3 ^ 40 * 1928402 * 2
def baseEnd_1928402 : Nat := 660131414061112901337631

theorem tailTrace_1928402 : CollatzResearch.WordTrace tailWord_1928402 prefixEnd_1928402 660131414061112901337631 := by
  unfold tailWord_1928402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583649789934093421556865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46889732773157582457484973 17583649789934093421556865)
  ·
    refine ⟨13187737342450570066167649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17583649789934093421556865 13187737342450570066167649)
    ·
      refine ⟨9890803006837927549625737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13187737342450570066167649 9890803006837927549625737)
      ·
        refine ⟨7418102255128445662219303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9890803006837927549625737 7418102255128445662219303)
        ·
          refine ⟨11127153382692668493328955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418102255128445662219303 11127153382692668493328955)
          ·
            refine ⟨16690730074039002739993433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127153382692668493328955 16690730074039002739993433)
            ·
              refine ⟨12518047555529252054995075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16690730074039002739993433 12518047555529252054995075)
              ·
                refine ⟨18777071333293878082492613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12518047555529252054995075 18777071333293878082492613)
                ·
                  refine ⟨3520700874992602140467365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18777071333293878082492613 3520700874992602140467365)
                  ·
                    refine ⟨660131414061112901337631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3520700874992602140467365 660131414061112901337631)
                    ·
                      rfl

theorem cell22_1928402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1928402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928402 prefixEnd_1928402 := by exact prefixLift 1928402
  have htrace : WordTrace (prefixWord ++ tailWord_1928402) baseStart_1928402 baseEnd_1928402 := by
    simpa [prefixWord, tailWord_1928402, baseEnd_1928402] using wordTrace_append hprefix tailTrace_1928402
  have hstable : (prefixWord ++ tailWord_1928402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928402).length < 2 ^ (prefixWord ++ tailWord_1928402).sum := by decide
  have hdescent : baseEnd_1928402 < baseStart_1928402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928406 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1928406 : Nat := 118140960795 + 1928406 * 2 ^ 59
def prefixEnd_1928406 : Nat := 4983230072969 + 3 ^ 40 * 1928406 * 2
def baseEnd_1928406 : Nat := 220044261114286074745873

theorem tailTrace_1928406 : CollatzResearch.WordTrace tailWord_1928406 prefixEnd_1928406 220044261114286074745873 := by
  unfold tailWord_1928406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395921565732617648085817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46889830034481254912915381 4395921565732617648085817)
  ·
    refine ⟨3296941174299463236064363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4395921565732617648085817 3296941174299463236064363)
    ·
      refine ⟨4945411761449194854096545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3296941174299463236064363 4945411761449194854096545)
      ·
        refine ⟨3709058821086896140572409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4945411761449194854096545 3709058821086896140572409)
        ·
          refine ⟨2781794115815172105429307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3709058821086896140572409 2781794115815172105429307)
          ·
            refine ⟨4172691173722758158143961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781794115815172105429307 4172691173722758158143961)
            ·
              refine ⟨3129518380292068618607971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172691173722758158143961 3129518380292068618607971)
              ·
                refine ⟨4694277570438102927911957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129518380292068618607971 4694277570438102927911957)
                ·
                  refine ⟨220044261114286074745873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4694277570438102927911957 220044261114286074745873)
                  ·
                    rfl

theorem cell22_1928406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1928406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928406 prefixEnd_1928406 := by exact prefixLift 1928406
  have htrace : WordTrace (prefixWord ++ tailWord_1928406) baseStart_1928406 baseEnd_1928406 := by
    simpa [prefixWord, tailWord_1928406, baseEnd_1928406] using wordTrace_append hprefix tailTrace_1928406
  have hstable : (prefixWord ++ tailWord_1928406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928406).length < 2 ^ (prefixWord ++ tailWord_1928406).sum := by decide
  have hdescent : baseEnd_1928406 < baseStart_1928406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928421 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_1928421 : Nat := 118140960795 + 1928421 * 2 ^ 59
def prefixEnd_1928421 : Nat := 4983230072969 + 3 ^ 40 * 1928421 * 2
def baseEnd_1928421 : Nat := 660137918149403185112573

theorem tailTrace_1928421 : CollatzResearch.WordTrace tailWord_1928421 prefixEnd_1928421 660137918149403185112573 := by
  unfold tailWord_1928421
  simp only [CollatzResearch.WordTrace]
  refine ⟨70335292146667539931169117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46890194764445026620779411 70335292146667539931169117)
  ·
    refine ⟨26375734555000327474188419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70335292146667539931169117 26375734555000327474188419)
    ·
      refine ⟨39563601832500491211282629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26375734555000327474188419 39563601832500491211282629)
      ·
        refine ⟨7418175343593842102115493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39563601832500491211282629 7418175343593842102115493)
        ·
          refine ⟨1390907876923845394146655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7418175343593842102115493 1390907876923845394146655)
          ·
            refine ⟨2086361815385768091219983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390907876923845394146655 2086361815385768091219983)
            ·
              refine ⟨3129542723078652136829975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086361815385768091219983 3129542723078652136829975)
              ·
                refine ⟨4694314084617978205244963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129542723078652136829975 4694314084617978205244963)
                ·
                  refine ⟨7041471126926967307867445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694314084617978205244963 7041471126926967307867445)
                  ·
                    refine ⟨660137918149403185112573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7041471126926967307867445 660137918149403185112573)
                    ·
                      rfl

theorem cell22_1928421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_1928421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928421 prefixEnd_1928421 := by exact prefixLift 1928421
  have htrace : WordTrace (prefixWord ++ tailWord_1928421) baseStart_1928421 baseEnd_1928421 := by
    simpa [prefixWord, tailWord_1928421, baseEnd_1928421] using wordTrace_append hprefix tailTrace_1928421
  have hstable : (prefixWord ++ tailWord_1928421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928421).length < 2 ^ (prefixWord ++ tailWord_1928421).sum := by decide
  have hdescent : baseEnd_1928421 < baseStart_1928421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928462 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1928462 : Nat := 118140960795 + 1928462 * 2 ^ 59
def prefixEnd_1928462 : Nat := 4983230072969 + 3 ^ 40 * 1928462 * 2
def baseEnd_1928462 : Nat := 220050651095764248279149

theorem tailTrace_1928462 : CollatzResearch.WordTrace tailWord_1928462 prefixEnd_1928462 220050651095764248279149 := by
  unfold tailWord_1928462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792098442439875491676455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46891191693012669288941093 8792098442439875491676455)
  ·
    refine ⟨13188147663659813237514683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8792098442439875491676455 13188147663659813237514683)
    ·
      refine ⟨19782221495489719856272025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13188147663659813237514683 19782221495489719856272025)
      ·
        refine ⟨14836666121617289892204019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19782221495489719856272025 14836666121617289892204019)
        ·
          refine ⟨22254999182425934838306029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14836666121617289892204019 22254999182425934838306029)
          ·
            refine ⟨8345624693409725564364761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22254999182425934838306029 8345624693409725564364761)
            ·
              refine ⟨6259218520057294173273571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8345624693409725564364761 6259218520057294173273571)
              ·
                refine ⟨9388827780085941259910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259218520057294173273571 9388827780085941259910357)
                ·
                  refine ⟨220050651095764248279149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9388827780085941259910357 220050651095764248279149)
                  ·
                    rfl

theorem cell22_1928462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1928462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928462 prefixEnd_1928462 := by exact prefixLift 1928462
  have htrace : WordTrace (prefixWord ++ tailWord_1928462) baseStart_1928462 baseEnd_1928462 := by
    simpa [prefixWord, tailWord_1928462, baseEnd_1928462] using wordTrace_append hprefix tailTrace_1928462
  have hstable : (prefixWord ++ tailWord_1928462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928462).length < 2 ^ (prefixWord ++ tailWord_1928462).sum := by decide
  have hdescent : baseEnd_1928462 < baseStart_1928462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928475 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_1928475 : Nat := 118140960795 + 1928475 * 2 ^ 59
def prefixEnd_1928475 : Nat := 4983230072969 + 3 ^ 40 * 1928475 * 2
def baseEnd_1928475 : Nat := 660156403452965044262407

theorem tailTrace_1928475 : CollatzResearch.WordTrace tailWord_1928475 prefixEnd_1928475 660156403452965044262407 := by
  unfold tailWord_1928475
  simp only [CollatzResearch.WordTrace]
  refine ⟨70337261688471907153634879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46891507792314604769089919 70337261688471907153634879)
  ·
    refine ⟨105505892532707860730452319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70337261688471907153634879 105505892532707860730452319)
    ·
      refine ⟨158258838799061791095678479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105505892532707860730452319 158258838799061791095678479)
      ·
        refine ⟨237388258198592686643517719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158258838799061791095678479 237388258198592686643517719)
        ·
          refine ⟨356082387297889029965276579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237388258198592686643517719 356082387297889029965276579)
          ·
            refine ⟨534123580946833544947914869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356082387297889029965276579 534123580946833544947914869)
            ·
              refine ⟨50074085713765644838867019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534123580946833544947914869 50074085713765644838867019)
              ·
                refine ⟨75111128570648467258300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50074085713765644838867019 75111128570648467258300529)
                ·
                  refine ⟨56333346427986350443725397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75111128570648467258300529 56333346427986350443725397)
                  ·
                    refine ⟨660156403452965044262407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56333346427986350443725397 660156403452965044262407)
                    ·
                      rfl

theorem cell22_1928475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_1928475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928475 prefixEnd_1928475 := by exact prefixLift 1928475
  have htrace : WordTrace (prefixWord ++ tailWord_1928475) baseStart_1928475 baseEnd_1928475 := by
    simpa [prefixWord, tailWord_1928475, baseEnd_1928475] using wordTrace_append hprefix tailTrace_1928475
  have hstable : (prefixWord ++ tailWord_1928475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928475).length < 2 ^ (prefixWord ++ tailWord_1928475).sum := by decide
  have hdescent : baseEnd_1928475 < baseStart_1928475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928479 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 5]
def baseStart_1928479 : Nat := 118140960795 + 1928479 * 2 ^ 59
def prefixEnd_1928479 : Nat := 4983230072969 + 3 ^ 40 * 1928479 * 2
def baseEnd_1928479 : Nat := 220052590911570122387465

theorem tailTrace_1928479 : CollatzResearch.WordTrace tailWord_1928479 prefixEnd_1928479 220052590911570122387465 := by
  unfold tailWord_1928479
  simp only [CollatzResearch.WordTrace]
  refine ⟨70337407580457415836780491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46891605053638277224520327 70337407580457415836780491)
  ·
    refine ⟨105506111370686123755170737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70337407580457415836780491 105506111370686123755170737)
    ·
      refine ⟨79129583528014592816378053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105506111370686123755170737 79129583528014592816378053)
      ·
        refine ⟨14836796911502736153070885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79129583528014592816378053 14836796911502736153070885)
        ·
          refine ⟨2781899420906763028700791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14836796911502736153070885 2781899420906763028700791)
          ·
            refine ⟨4172849131360144543051187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781899420906763028700791 4172849131360144543051187)
            ·
              refine ⟨6259273697040216814576781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172849131360144543051187 6259273697040216814576781)
              ·
                refine ⟨2347227636390081305466293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6259273697040216814576781 2347227636390081305466293)
                ·
                  refine ⟨220052590911570122387465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2347227636390081305466293 220052590911570122387465)
                  ·
                    rfl

theorem cell22_1928479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 5].length) (baseStart_1928479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928479 prefixEnd_1928479 := by exact prefixLift 1928479
  have htrace : WordTrace (prefixWord ++ tailWord_1928479) baseStart_1928479 baseEnd_1928479 := by
    simpa [prefixWord, tailWord_1928479, baseEnd_1928479] using wordTrace_append hprefix tailTrace_1928479
  have hstable : (prefixWord ++ tailWord_1928479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928479).length < 2 ^ (prefixWord ++ tailWord_1928479).sum := by decide
  have hdescent : baseEnd_1928479 < baseStart_1928479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928537 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_1928537 : Nat := 118140960795 + 1928537 * 2 ^ 59
def prefixEnd_1928537 : Nat := 4983230072969 + 3 ^ 40 * 1928537 * 2
def baseEnd_1928537 : Nat := 660177627320017549212217

theorem tailTrace_1928537 : CollatzResearch.WordTrace tailWord_1928537 prefixEnd_1928537 660177627320017549212217 := by
  unfold tailWord_1928537
  simp only [CollatzResearch.WordTrace]
  refine ⟨70339523014247291742391865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46893015342831527828261243 70339523014247291742391865)
  ·
    refine ⟨52754642260685468806793899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70339523014247291742391865 52754642260685468806793899)
    ·
      refine ⟨79131963391028203210190849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52754642260685468806793899 79131963391028203210190849)
      ·
        refine ⟨59348972543271152407643137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79131963391028203210190849 59348972543271152407643137)
        ·
          refine ⟨44511729407453364305732353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59348972543271152407643137 44511729407453364305732353)
          ·
            refine ⟨33383797055590023229299265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44511729407453364305732353 33383797055590023229299265)
            ·
              refine ⟨25037847791692517421974449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33383797055590023229299265 25037847791692517421974449)
              ·
                refine ⟨18778385843769388066480837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25037847791692517421974449 18778385843769388066480837)
                ·
                  refine ⟨3520947345706760262465157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18778385843769388066480837 3520947345706760262465157)
                  ·
                    refine ⟨660177627320017549212217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3520947345706760262465157 660177627320017549212217)
                    ·
                      rfl

theorem cell22_1928537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_1928537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928537 prefixEnd_1928537 := by exact prefixLift 1928537
  have htrace : WordTrace (prefixWord ++ tailWord_1928537) baseStart_1928537 baseEnd_1928537 := by
    simpa [prefixWord, tailWord_1928537, baseEnd_1928537] using wordTrace_append hprefix tailTrace_1928537
  have hstable : (prefixWord ++ tailWord_1928537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928537).length < 2 ^ (prefixWord ++ tailWord_1928537).sum := by decide
  have hdescent : baseEnd_1928537 < baseStart_1928537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928590 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_1928590 : Nat := 118140960795 + 1928590 * 2 ^ 59
def prefixEnd_1928590 : Nat := 4983230072969 + 3 ^ 40 * 1928590 * 2
def baseEnd_1928590 : Nat := 660195770303143077637055

theorem tailTrace_1928590 : CollatzResearch.WordTrace tailWord_1928590 prefixEnd_1928590 660195770303143077637055 := by
  unfold tailWord_1928590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792682010381910224258903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46894304055370187862714149 8792682010381910224258903)
  ·
    refine ⟨13189023015572865336388355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8792682010381910224258903 13189023015572865336388355)
    ·
      refine ⟨19783534523359298004582533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13189023015572865336388355 19783534523359298004582533)
      ·
        refine ⟨3709412723129868375859225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19783534523359298004582533 3709412723129868375859225)
        ·
          refine ⟨2782059542347401281894419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3709412723129868375859225 2782059542347401281894419)
          ·
            refine ⟨4173089313521101922841629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782059542347401281894419 4173089313521101922841629)
            ·
              refine ⟨1564908492570413221065611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4173089313521101922841629 1564908492570413221065611)
              ·
                refine ⟨2347362738855619831598417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564908492570413221065611 2347362738855619831598417)
                ·
                  refine ⟨1760522054141714873698813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347362738855619831598417 1760522054141714873698813)
                  ·
                    refine ⟨660195770303143077637055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760522054141714873698813 660195770303143077637055)
                    ·
                      rfl

theorem cell22_1928590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_1928590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928590 prefixEnd_1928590 := by exact prefixLift 1928590
  have htrace : WordTrace (prefixWord ++ tailWord_1928590) baseStart_1928590 baseEnd_1928590 := by
    simpa [prefixWord, tailWord_1928590, baseEnd_1928590] using wordTrace_append hprefix tailTrace_1928590
  have hstable : (prefixWord ++ tailWord_1928590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928590).length < 2 ^ (prefixWord ++ tailWord_1928590).sum := by decide
  have hdescent : baseEnd_1928590 < baseStart_1928590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928708 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1928708 : Nat := 118140960795 + 1928708 * 2 ^ 59
def prefixEnd_1928708 : Nat := 4983230072969 + 3 ^ 40 * 1928708 * 2
def baseEnd_1928708 : Nat := 660236164114630103186693

theorem tailTrace_1928708 : CollatzResearch.WordTrace tailWord_1928708 prefixEnd_1928708 660236164114630103186693 := by
  unfold tailWord_1928708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35172879948313893973433389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46897173264418525297911185 35172879948313893973433389)
  ·
    refine ⟨13189829980617710240037521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35172879948313893973433389 13189829980617710240037521)
    ·
      refine ⟨9892372485463282680028141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13189829980617710240037521 9892372485463282680028141)
      ·
        refine ⟨3709639682048731005010553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9892372485463282680028141 3709639682048731005010553)
        ·
          refine ⟨2782229761536548253757915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3709639682048731005010553 2782229761536548253757915)
          ·
            refine ⟨4173344642304822380636873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782229761536548253757915 4173344642304822380636873)
            ·
              refine ⟨3130008481728616785477655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173344642304822380636873 3130008481728616785477655)
              ·
                refine ⟨4695012722592925178216483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130008481728616785477655 4695012722592925178216483)
                ·
                  refine ⟨7042519083889387767324725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695012722592925178216483 7042519083889387767324725)
                  ·
                    refine ⟨660236164114630103186693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7042519083889387767324725 660236164114630103186693)
                    ·
                      rfl

theorem cell22_1928708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1928708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928708 prefixEnd_1928708 := by exact prefixLift 1928708
  have htrace : WordTrace (prefixWord ++ tailWord_1928708) baseStart_1928708 baseEnd_1928708 := by
    simpa [prefixWord, tailWord_1928708, baseEnd_1928708] using wordTrace_append hprefix tailTrace_1928708
  have hstable : (prefixWord ++ tailWord_1928708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928708).length < 2 ^ (prefixWord ++ tailWord_1928708).sum := by decide
  have hdescent : baseEnd_1928708 < baseStart_1928708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928794 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_1928794 : Nat := 118140960795 + 1928794 * 2 ^ 59
def prefixEnd_1928794 : Nat := 4983230072969 + 3 ^ 40 * 1928794 * 2
def baseEnd_1928794 : Nat := 220088534557384848512143

theorem tailTrace_1928794 : CollatzResearch.WordTrace tailWord_1928794 prefixEnd_1928794 220088534557384848512143 := by
  unfold tailWord_1928794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587224143579056158624359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46899264382877483089664957 17587224143579056158624359)
  ·
    refine ⟨26380836215368584237936539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17587224143579056158624359 26380836215368584237936539)
    ·
      refine ⟨39571254323052876356904809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26380836215368584237936539 39571254323052876356904809)
      ·
        refine ⟨29678440742289657267678607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39571254323052876356904809 29678440742289657267678607)
        ·
          refine ⟨44517661113434485901517911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29678440742289657267678607 44517661113434485901517911)
          ·
            refine ⟨66776491670151728852276867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44517661113434485901517911 66776491670151728852276867)
            ·
              refine ⟨100164737505227593278415301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66776491670151728852276867 100164737505227593278415301)
              ·
                refine ⟨18780888282230173739702869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100164737505227593278415301 18780888282230173739702869)
                ·
                  refine ⟨220088534557384848512143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18780888282230173739702869 220088534557384848512143)
                  ·
                    rfl

theorem cell22_1928794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_1928794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928794 prefixEnd_1928794 := by exact prefixLift 1928794
  have htrace : WordTrace (prefixWord ++ tailWord_1928794) baseStart_1928794 baseEnd_1928794 := by
    simpa [prefixWord, tailWord_1928794, baseEnd_1928794] using wordTrace_append hprefix tailTrace_1928794
  have hstable : (prefixWord ++ tailWord_1928794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928794).length < 2 ^ (prefixWord ++ tailWord_1928794).sum := by decide
  have hdescent : baseEnd_1928794 < baseStart_1928794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928826 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1928826 : Nat := 118140960795 + 1928826 * 2 ^ 59
def prefixEnd_1928826 : Nat := 4983230072969 + 3 ^ 40 * 1928826 * 2
def baseEnd_1928826 : Nat := 660276557926117128736331

theorem tailTrace_1928826 : CollatzResearch.WordTrace tailWord_1928826 prefixEnd_1928826 660276557926117128736331 := by
  unfold tailWord_1928826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587515927550073524915583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46900042473466862733108221 17587515927550073524915583)
  ·
    refine ⟨26381273891325110287373375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17587515927550073524915583 26381273891325110287373375)
    ·
      refine ⟨39571910836987665431060063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26381273891325110287373375 39571910836987665431060063)
      ·
        refine ⟨59357866255481498146590095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39571910836987665431060063 59357866255481498146590095)
        ·
          refine ⟨89036799383222247219885143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59357866255481498146590095 89036799383222247219885143)
          ·
            refine ⟨133555199074833370829827715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89036799383222247219885143 133555199074833370829827715)
            ·
              refine ⟨200332798612250056244741573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133555199074833370829827715 200332798612250056244741573)
              ·
                refine ⟨37562399739796885545889045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200332798612250056244741573 37562399739796885545889045)
                ·
                  refine ⟨1760737487802979009963549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37562399739796885545889045 1760737487802979009963549)
                  ·
                    refine ⟨660276557926117128736331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760737487802979009963549 660276557926117128736331)
                    ·
                      rfl

theorem cell22_1928826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1928826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928826 prefixEnd_1928826 := by exact prefixLift 1928826
  have htrace : WordTrace (prefixWord ++ tailWord_1928826) baseStart_1928826 baseEnd_1928826 := by
    simpa [prefixWord, tailWord_1928826, baseEnd_1928826] using wordTrace_append hprefix tailTrace_1928826
  have hstable : (prefixWord ++ tailWord_1928826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928826).length < 2 ^ (prefixWord ++ tailWord_1928826).sum := by decide
  have hdescent : baseEnd_1928826 < baseStart_1928826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928841 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_1928841 : Nat := 118140960795 + 1928841 * 2 ^ 59
def prefixEnd_1928841 : Nat := 4983230072969 + 3 ^ 40 * 1928841 * 2
def baseEnd_1928841 : Nat := 660281692732662089611285

theorem tailTrace_1928841 : CollatzResearch.WordTrace tailWord_1928841 prefixEnd_1928841 660281692732662089611285 := by
  unfold tailWord_1928841
  simp only [CollatzResearch.WordTrace]
  refine ⟨70350610805145951661458377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46900407203430634440972251 70350610805145951661458377)
  ·
    refine ⟨52762958103859463746093783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70350610805145951661458377 52762958103859463746093783)
    ·
      refine ⟨79144437155789195619140675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52762958103859463746093783 79144437155789195619140675)
      ·
        refine ⟨118716655733683793428711013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79144437155789195619140675 118716655733683793428711013)
        ·
          refine ⟨22259372950065711267883315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118716655733683793428711013 22259372950065711267883315)
          ·
            refine ⟨33389059425098566901824973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22259372950065711267883315 33389059425098566901824973)
            ·
              refine ⟨12520897284411962588184365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33389059425098566901824973 12520897284411962588184365)
              ·
                refine ⟨4695336481654485970569137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12520897284411962588184365 4695336481654485970569137)
                ·
                  refine ⟨3521502361240864477926853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695336481654485970569137 3521502361240864477926853)
                  ·
                    refine ⟨660281692732662089611285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3521502361240864477926853 660281692732662089611285)
                    ·
                      rfl

theorem cell22_1928841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_1928841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928841 prefixEnd_1928841 := by exact prefixLift 1928841
  have htrace : WordTrace (prefixWord ++ tailWord_1928841) baseStart_1928841 baseEnd_1928841 := by
    simpa [prefixWord, tailWord_1928841, baseEnd_1928841] using wordTrace_append hprefix tailTrace_1928841
  have hstable : (prefixWord ++ tailWord_1928841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928841).length < 2 ^ (prefixWord ++ tailWord_1928841).sum := by decide
  have hdescent : baseEnd_1928841 < baseStart_1928841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928862 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1928862 : Nat := 118140960795 + 1928862 * 2 ^ 59
def prefixEnd_1928862 : Nat := 4983230072969 + 3 ^ 40 * 1928862 * 2
def baseEnd_1928862 : Nat := 220096293820608344945407

theorem tailTrace_1928862 : CollatzResearch.WordTrace tailWord_1928862 prefixEnd_1928862 220096293820608344945407 := by
  unfold tailWord_1928862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8793922092258734030996605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46900917825379914831981893 8793922092258734030996605)
  ·
    refine ⟨3297720784597025261623727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8793922092258734030996605 3297720784597025261623727)
    ·
      refine ⟨4946581176895537892435591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3297720784597025261623727 4946581176895537892435591)
      ·
        refine ⟨7419871765343306838653387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946581176895537892435591 7419871765343306838653387)
        ·
          refine ⟨11129807648014960257980081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419871765343306838653387 11129807648014960257980081)
          ·
            refine ⟨8347355736011220193485061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11129807648014960257980081 8347355736011220193485061)
            ·
              refine ⟨1565129200502103786278449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8347355736011220193485061 1565129200502103786278449)
              ·
                refine ⟨1173846900376577839708837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565129200502103786278449 1173846900376577839708837)
                ·
                  refine ⟨220096293820608344945407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173846900376577839708837 220096293820608344945407)
                  ·
                    rfl

theorem cell22_1928862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1928862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928862 prefixEnd_1928862 := by exact prefixLift 1928862
  have htrace : WordTrace (prefixWord ++ tailWord_1928862) baseStart_1928862 baseEnd_1928862 := by
    simpa [prefixWord, tailWord_1928862, baseEnd_1928862] using wordTrace_append hprefix tailTrace_1928862
  have hstable : (prefixWord ++ tailWord_1928862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928862).length < 2 ^ (prefixWord ++ tailWord_1928862).sum := by decide
  have hdescent : baseEnd_1928862 < baseStart_1928862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928898 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1928898 : Nat := 118140960795 + 1928898 * 2 ^ 59
def prefixEnd_1928898 : Nat := 4983230072969 + 3 ^ 40 * 1928898 * 2
def baseEnd_1928898 : Nat := 660301204997532940936111

theorem tailTrace_1928898 : CollatzResearch.WordTrace tailWord_1928898 prefixEnd_1928898 660301204997532940936111 := by
  unfold tailWord_1928898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17588172441484862599070837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46901793177292966930855565 17588172441484862599070837)
  ·
    refine ⟨1648891166389205868662891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17588172441484862599070837 1648891166389205868662891)
    ·
      refine ⟨2473336749583808802994337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648891166389205868662891 2473336749583808802994337)
      ·
        refine ⟨1855002562187856602245753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2473336749583808802994337 1855002562187856602245753)
        ·
          refine ⟨1391251921640892451684315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855002562187856602245753 1391251921640892451684315)
          ·
            refine ⟨2086877882461338677526473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391251921640892451684315 2086877882461338677526473)
            ·
              refine ⟨1565158411846004008144855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086877882461338677526473 1565158411846004008144855)
              ·
                refine ⟨2347737617769006012217283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565158411846004008144855 2347737617769006012217283)
                ·
                  refine ⟨3521606426653509018325925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347737617769006012217283 3521606426653509018325925)
                  ·
                    refine ⟨660301204997532940936111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3521606426653509018325925 660301204997532940936111)
                    ·
                      rfl

theorem cell22_1928898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1928898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928898 prefixEnd_1928898 := by exact prefixLift 1928898
  have htrace : WordTrace (prefixWord ++ tailWord_1928898) baseStart_1928898 baseEnd_1928898 := by
    simpa [prefixWord, tailWord_1928898, baseEnd_1928898] using wordTrace_append hprefix tailTrace_1928898
  have hstable : (prefixWord ++ tailWord_1928898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928898).length < 2 ^ (prefixWord ++ tailWord_1928898).sum := by decide
  have hdescent : baseEnd_1928898 < baseStart_1928898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928973 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1928973 : Nat := 118140960795 + 1928973 * 2 ^ 59
def prefixEnd_1928973 : Nat := 4983230072969 + 3 ^ 40 * 1928973 * 2
def baseEnd_1928973 : Nat := 660326879030257745310881

theorem tailTrace_1928973 : CollatzResearch.WordTrace tailWord_1928973 prefixEnd_1928973 660326879030257745310881 := by
  unfold tailWord_1928973
  simp only [CollatzResearch.WordTrace]
  refine ⟨70355425240667738205263573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46903616827111825470175715 70355425240667738205263573)
  ·
    refine ⟨1648955279078150114185865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 70355425240667738205263573 1648955279078150114185865)
    ·
      refine ⟨1236716459308612585639399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1648955279078150114185865 1236716459308612585639399)
      ·
        refine ⟨1855074688962918878459099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236716459308612585639399 1855074688962918878459099)
        ·
          refine ⟨2782612033444378317688649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855074688962918878459099 2782612033444378317688649)
          ·
            refine ⟨2086959025083283738266487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2782612033444378317688649 2086959025083283738266487)
            ·
              refine ⟨3130438537624925607399731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086959025083283738266487 3130438537624925607399731)
              ·
                refine ⟨4695657806437388411099597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130438537624925607399731 4695657806437388411099597)
                ·
                  refine ⟨1760871677414020654162349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4695657806437388411099597 1760871677414020654162349)
                  ·
                    refine ⟨660326879030257745310881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760871677414020654162349 660326879030257745310881)
                    ·
                      rfl

theorem cell22_1928973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1928973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1928973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1928973 prefixEnd_1928973 := by exact prefixLift 1928973
  have htrace : WordTrace (prefixWord ++ tailWord_1928973) baseStart_1928973 baseEnd_1928973 := by
    simpa [prefixWord, tailWord_1928973, baseEnd_1928973] using wordTrace_append hprefix tailTrace_1928973
  have hstable : (prefixWord ++ tailWord_1928973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928973).length < 2 ^ (prefixWord ++ tailWord_1928973).sum := by decide
  have hdescent : baseEnd_1928973 < baseStart_1928973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929010 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1929010 : Nat := 118140960795 + 1929010 * 2 ^ 59
def prefixEnd_1929010 : Nat := 4983230072969 + 3 ^ 40 * 1929010 * 2
def baseEnd_1929010 : Nat := 660339544886401982135767

theorem tailTrace_1929010 : CollatzResearch.WordTrace tailWord_1929010 prefixEnd_1929010 660339544886401982135767 := by
  unfold tailWord_1929010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17589193685383423381090121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46904516494355795682906989 17589193685383423381090121)
  ·
    refine ⟨13191895264037567535817591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17589193685383423381090121 13191895264037567535817591)
    ·
      refine ⟨19787842896056351303726387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191895264037567535817591 19787842896056351303726387)
      ·
        refine ⟨29681764344084526955589581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19787842896056351303726387 29681764344084526955589581)
        ·
          refine ⟨11130661629031697608346093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29681764344084526955589581 11130661629031697608346093)
          ·
            refine ⟨4173998110886886603129785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11130661629031697608346093 4173998110886886603129785)
            ·
              refine ⟨3130498583165164952347339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173998110886886603129785 3130498583165164952347339)
              ·
                refine ⟨4695747874747747428521009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130498583165164952347339 4695747874747747428521009)
                ·
                  refine ⟨3521810906060810571390757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695747874747747428521009 3521810906060810571390757)
                  ·
                    refine ⟨660339544886401982135767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3521810906060810571390757 660339544886401982135767)
                    ·
                      rfl

theorem cell22_1929010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1929010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929010 prefixEnd_1929010 := by exact prefixLift 1929010
  have htrace : WordTrace (prefixWord ++ tailWord_1929010) baseStart_1929010 baseEnd_1929010 := by
    simpa [prefixWord, tailWord_1929010, baseEnd_1929010] using wordTrace_append hprefix tailTrace_1929010
  have hstable : (prefixWord ++ tailWord_1929010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929010).length < 2 ^ (prefixWord ++ tailWord_1929010).sum := by decide
  have hdescent : baseEnd_1929010 < baseStart_1929010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929117 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1929117 : Nat := 118140960795 + 1929117 * 2 ^ 59
def prefixEnd_1929117 : Nat := 4983230072969 + 3 ^ 40 * 1929117 * 2
def baseEnd_1929117 : Nat := 660376173173089369710439

theorem tailTrace_1929117 : CollatzResearch.WordTrace tailWord_1929117 prefixEnd_1929117 660376173173089369710439 := by
  unfold tailWord_1929117
  simp only [CollatzResearch.WordTrace]
  refine ⟨70360677352146050798505605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46907118234764033865670403 70360677352146050798505605)
  ·
    refine ⟨13192627003527384524719801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70360677352146050798505605 13192627003527384524719801)
    ·
      refine ⟨9894470252645538393539851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13192627003527384524719801 9894470252645538393539851)
      ·
        refine ⟨14841705378968307590309777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9894470252645538393539851 14841705378968307590309777)
        ·
          refine ⟨11131279034226230692732333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14841705378968307590309777 11131279034226230692732333)
          ·
            refine ⟨4174229637834836509774625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11131279034226230692732333 4174229637834836509774625)
            ·
              refine ⟨3130672228376127382330969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174229637834836509774625 3130672228376127382330969)
              ·
                refine ⟨2348004171282095536748227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130672228376127382330969 2348004171282095536748227)
                ·
                  refine ⟨3522006256923143305122341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348004171282095536748227 3522006256923143305122341)
                  ·
                    refine ⟨660376173173089369710439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522006256923143305122341 660376173173089369710439)
                    ·
                      rfl

theorem cell22_1929117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1929117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929117 prefixEnd_1929117 := by exact prefixLift 1929117
  have htrace : WordTrace (prefixWord ++ tailWord_1929117) baseStart_1929117 baseEnd_1929117 := by
    simpa [prefixWord, tailWord_1929117, baseEnd_1929117] using wordTrace_append hprefix tailTrace_1929117
  have hstable : (prefixWord ++ tailWord_1929117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929117).length < 2 ^ (prefixWord ++ tailWord_1929117).sum := by decide
  have hdescent : baseEnd_1929117 < baseStart_1929117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929145 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_1929145 : Nat := 118140960795 + 1929145 * 2 ^ 59
def prefixEnd_1929145 : Nat := 4983230072969 + 3 ^ 40 * 1929145 * 2
def baseEnd_1929145 : Nat := 660385758145306630010353

theorem tailTrace_1929145 : CollatzResearch.WordTrace tailWord_1929145 prefixEnd_1929145 660385758145306630010353 := by
  unfold tailWord_1929145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70361698596044611580524889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46907799064029741053683259 70361698596044611580524889)
  ·
    refine ⟨52771273947033458685393667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70361698596044611580524889 52771273947033458685393667)
    ·
      refine ⟨79156910920550188028090501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52771273947033458685393667 79156910920550188028090501)
      ·
        refine ⟨14841920797603160255266969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79156910920550188028090501 14841920797603160255266969)
        ·
          refine ⟨11131440598202370191450227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14841920797603160255266969 11131440598202370191450227)
          ·
            refine ⟨16697160897303555287175341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131440598202370191450227 16697160897303555287175341)
            ·
              refine ⟨6261435336488833232690753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16697160897303555287175341 6261435336488833232690753)
              ·
                refine ⟨4696076502366624924518065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261435336488833232690753 4696076502366624924518065)
                ·
                  refine ⟨3522057376774968693388549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696076502366624924518065 3522057376774968693388549)
                  ·
                    refine ⟨660385758145306630010353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522057376774968693388549 660385758145306630010353)
                    ·
                      rfl

theorem cell22_1929145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_1929145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929145 prefixEnd_1929145 := by exact prefixLift 1929145
  have htrace : WordTrace (prefixWord ++ tailWord_1929145) baseStart_1929145 baseEnd_1929145 := by
    simpa [prefixWord, tailWord_1929145, baseEnd_1929145] using wordTrace_append hprefix tailTrace_1929145
  have hstable : (prefixWord ++ tailWord_1929145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929145).length < 2 ^ (prefixWord ++ tailWord_1929145).sum := by decide
  have hdescent : baseEnd_1929145 < baseStart_1929145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929149 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 4]
def baseStart_1929149 : Nat := 118140960795 + 1929149 * 2 ^ 59
def prefixEnd_1929149 : Nat := 4983230072969 + 3 ^ 40 * 1929149 * 2
def baseEnd_1929149 : Nat := 220129042475683984303447

theorem tailTrace_1929149 : CollatzResearch.WordTrace tailWord_1929149 prefixEnd_1929149 220129042475683984303447 := by
  unfold tailWord_1929149
  simp only [CollatzResearch.WordTrace]
  refine ⟨70361844488030120263670501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46907896325353413509113667 70361844488030120263670501)
  ·
    refine ⟨13192845841505647549438219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70361844488030120263670501 13192845841505647549438219)
    ·
      refine ⟨19789268762258471324157329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13192845841505647549438219 19789268762258471324157329)
      ·
        refine ⟨14841951571693853493117997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19789268762258471324157329 14841951571693853493117997)
        ·
          refine ⟨5565731839385195059919249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14841951571693853493117997 5565731839385195059919249)
          ·
            refine ⟨4174298879538896294939437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5565731839385195059919249 4174298879538896294939437)
            ·
              refine ⟨1565362079827086110602289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4174298879538896294939437 1565362079827086110602289)
              ·
                refine ⟨1174021559870314582951717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565362079827086110602289 1174021559870314582951717)
                ·
                  refine ⟨220129042475683984303447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174021559870314582951717 220129042475683984303447)
                  ·
                    rfl

theorem cell22_1929149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_1929149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929149 prefixEnd_1929149 := by exact prefixLift 1929149
  have htrace : WordTrace (prefixWord ++ tailWord_1929149) baseStart_1929149 baseEnd_1929149 := by
    simpa [prefixWord, tailWord_1929149, baseEnd_1929149] using wordTrace_append hprefix tailTrace_1929149
  have hstable : (prefixWord ++ tailWord_1929149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929149).length < 2 ^ (prefixWord ++ tailWord_1929149).sum := by decide
  have hdescent : baseEnd_1929149 < baseStart_1929149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929160 : List Nat := [2, 1, 3, 1, 4, 2, 2, 7]
def baseStart_1929160 : Nat := 118140960795 + 1929160 * 2 ^ 59
def prefixEnd_1929160 : Nat := 4983230072969 + 3 ^ 40 * 1929160 * 2
def baseEnd_1929160 : Nat := 73376765883539065653923

theorem tailTrace_1929160 : CollatzResearch.WordTrace tailWord_1929160 prefixEnd_1929160 73376765883539065653923 := by
  unfold tailWord_1929160
  simp only [CollatzResearch.WordTrace]
  refine ⟨35181122845495134571160467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46908163793993512761547289 35181122845495134571160467)
  ·
    refine ⟨52771684268242701856740701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35181122845495134571160467 52771684268242701856740701)
    ·
      refine ⟨19789381600591013196277763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52771684268242701856740701 19789381600591013196277763)
      ·
        refine ⟨29684072400886519794416645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19789381600591013196277763 29684072400886519794416645)
        ·
          refine ⟨5565763575166222461453121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29684072400886519794416645 5565763575166222461453121)
          ·
            refine ⟨4174322681374666846089841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5565763575166222461453121 4174322681374666846089841)
            ·
              refine ⟨3130742011031000134567381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174322681374666846089841 3130742011031000134567381)
              ·
                refine ⟨73376765883539065653923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3130742011031000134567381 73376765883539065653923)
                ·
                  rfl

theorem cell22_1929160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_1929160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929160 prefixEnd_1929160 := by exact prefixLift 1929160
  have htrace : WordTrace (prefixWord ++ tailWord_1929160) baseStart_1929160 baseEnd_1929160 := by
    simpa [prefixWord, tailWord_1929160, baseEnd_1929160] using wordTrace_append hprefix tailTrace_1929160
  have hstable : (prefixWord ++ tailWord_1929160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929160).length < 2 ^ (prefixWord ++ tailWord_1929160).sum := by decide
  have hdescent : baseEnd_1929160 < baseStart_1929160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929164 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_1929164 : Nat := 118140960795 + 1929164 * 2 ^ 59
def prefixEnd_1929164 : Nat := 4983230072969 + 3 ^ 40 * 1929164 * 2
def baseEnd_1929164 : Nat := 660392262233596913785295

theorem tailTrace_1929164 : CollatzResearch.WordTrace tailWord_1929164 prefixEnd_1929164 660392262233596913785295 := by
  unfold tailWord_1929164
  simp only [CollatzResearch.WordTrace]
  refine ⟨35181195791487888912733273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46908261055317185216977697 35181195791487888912733273)
  ·
    refine ⟨26385896843615916684549955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35181195791487888912733273 26385896843615916684549955)
    ·
      refine ⟨39578845265423875026824933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26385896843615916684549955 39578845265423875026824933)
      ·
        refine ⟨7421033487266976567529675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39578845265423875026824933 7421033487266976567529675)
        ·
          refine ⟨11131550230900464851294513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421033487266976567529675 11131550230900464851294513)
          ·
            refine ⟨8348662673175348638470885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11131550230900464851294513 8348662673175348638470885)
            ·
              refine ⟨1565374251220377869713291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8348662673175348638470885 1565374251220377869713291)
              ·
                refine ⟨2348061376830566804569937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565374251220377869713291 2348061376830566804569937)
                ·
                  refine ⟨1761046032622925103427453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348061376830566804569937 1761046032622925103427453)
                  ·
                    refine ⟨660392262233596913785295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761046032622925103427453 660392262233596913785295)
                    ·
                      rfl

theorem cell22_1929164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_1929164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929164 prefixEnd_1929164 := by exact prefixLift 1929164
  have htrace : WordTrace (prefixWord ++ tailWord_1929164) baseStart_1929164 baseEnd_1929164 := by
    simpa [prefixWord, tailWord_1929164, baseEnd_1929164] using wordTrace_append hprefix tailTrace_1929164
  have hstable : (prefixWord ++ tailWord_1929164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929164).length < 2 ^ (prefixWord ++ tailWord_1929164).sum := by decide
  have hdescent : baseEnd_1929164 < baseStart_1929164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929175 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 5, 3]
def baseStart_1929175 : Nat := 118140960795 + 1929175 * 2 ^ 59
def prefixEnd_1929175 : Nat := 4983230072969 + 3 ^ 40 * 1929175 * 2
def baseEnd_1929175 : Nat := 660396027758396551760261

theorem tailTrace_1929175 : CollatzResearch.WordTrace tailWord_1929175 prefixEnd_1929175 660396027758396551760261 := by
  unfold tailWord_1929175
  simp only [CollatzResearch.WordTrace]
  refine ⟨70362792785935926704116979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46908528523957284469411319 70362792785935926704116979)
  ·
    refine ⟨105544189178903890056175469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70362792785935926704116979 105544189178903890056175469)
    ·
      refine ⟨39579070942088958771065801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105544189178903890056175469 39579070942088958771065801)
      ·
        refine ⟨29684303206566719078299351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39579070942088958771065801 29684303206566719078299351)
        ·
          refine ⟨44526454809850078617449027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29684303206566719078299351 44526454809850078617449027)
          ·
            refine ⟨66789682214775117926173541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44526454809850078617449027 66789682214775117926173541)
            ·
              refine ⟨12523065415270334611157539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66789682214775117926173541 12523065415270334611157539)
              ·
                refine ⟨18784598122905501916736309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12523065415270334611157539 18784598122905501916736309)
                ·
                  refine ⟨1761056074022390804694029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18784598122905501916736309 1761056074022390804694029)
                  ·
                    refine ⟨660396027758396551760261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761056074022390804694029 660396027758396551760261)
                    ·
                      rfl

theorem cell22_1929175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_1929175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929175 prefixEnd_1929175 := by exact prefixLift 1929175
  have htrace : WordTrace (prefixWord ++ tailWord_1929175) baseStart_1929175 baseEnd_1929175 := by
    simpa [prefixWord, tailWord_1929175, baseEnd_1929175] using wordTrace_append hprefix tailTrace_1929175
  have hstable : (prefixWord ++ tailWord_1929175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929175).length < 2 ^ (prefixWord ++ tailWord_1929175).sum := by decide
  have hdescent : baseEnd_1929175 < baseStart_1929175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929203 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_1929203 : Nat := 118140960795 + 1929203 * 2 ^ 59
def prefixEnd_1929203 : Nat := 4983230072969 + 3 ^ 40 * 1929203 * 2
def baseEnd_1929203 : Nat := 660405612730613812060175

theorem tailTrace_1929203 : CollatzResearch.WordTrace tailWord_1929203 prefixEnd_1929203 660405612730613812060175 := by
  unfold tailWord_1929203
  simp only [CollatzResearch.WordTrace]
  refine ⟨70363814029834487486136263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46909209353222991657424175 70363814029834487486136263)
  ·
    refine ⟨105545721044751731229204395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70363814029834487486136263 105545721044751731229204395)
    ·
      refine ⟨158318581567127596843806593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105545721044751731229204395 158318581567127596843806593)
      ·
        refine ⟨118738936175345697632854945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158318581567127596843806593 118738936175345697632854945)
        ·
          refine ⟨89054202131509273224641209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118738936175345697632854945 89054202131509273224641209)
          ·
            refine ⟨66790651598631954918480907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89054202131509273224641209 66790651598631954918480907)
            ·
              refine ⟨100185977397947932377721361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66790651598631954918480907 100185977397947932377721361)
              ·
                refine ⟨75139483048460949283291021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100185977397947932377721361 75139483048460949283291021)
                ·
                  refine ⟨28177306143172855981234133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75139483048460949283291021 28177306143172855981234133)
                  ·
                    refine ⟨660405612730613812060175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28177306143172855981234133 660405612730613812060175)
                    ·
                      rfl

theorem cell22_1929203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_1929203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929203 prefixEnd_1929203 := by exact prefixLift 1929203
  have htrace : WordTrace (prefixWord ++ tailWord_1929203) baseStart_1929203 baseEnd_1929203 := by
    simpa [prefixWord, tailWord_1929203, baseEnd_1929203] using wordTrace_append hprefix tailTrace_1929203
  have hstable : (prefixWord ++ tailWord_1929203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929203).length < 2 ^ (prefixWord ++ tailWord_1929203).sum := by decide
  have hdescent : baseEnd_1929203 < baseStart_1929203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929209 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 1, 3]
def baseStart_1929209 : Nat := 118140960795 + 1929209 * 2 ^ 59
def prefixEnd_1929209 : Nat := 4983230072969 + 3 ^ 40 * 1929209 * 2
def baseEnd_1929209 : Nat := 660407666653231796410157

theorem tailTrace_1929209 : CollatzResearch.WordTrace tailWord_1929209 prefixEnd_1929209 660407666653231796410157 := by
  unfold tailWord_1929209
  simp only [CollatzResearch.WordTrace]
  refine ⟨70364032867812750510854681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46909355245208500340569787 70364032867812750510854681)
  ·
    refine ⟨52773024650859562883141011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70364032867812750510854681 52773024650859562883141011)
    ·
      refine ⟨79159536976289344324711517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52773024650859562883141011 79159536976289344324711517)
      ·
        refine ⟨29684826366108504121766819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79159536976289344324711517 29684826366108504121766819)
        ·
          refine ⟨44527239549162756182650229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29684826366108504121766819 44527239549162756182650229)
          ·
            refine ⟨4174428707734008392123459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44527239549162756182650229 4174428707734008392123459)
            ·
              refine ⟨6261643061601012588185189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174428707734008392123459 6261643061601012588185189)
              ·
                refine ⟨1174058074050189860284723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6261643061601012588185189 1174058074050189860284723)
                ·
                  refine ⟨1761087111075284790427085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174058074050189860284723 1761087111075284790427085)
                  ·
                    refine ⟨660407666653231796410157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761087111075284790427085 660407666653231796410157)
                    ·
                      rfl

theorem cell22_1929209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_1929209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929209 prefixEnd_1929209 := by exact prefixLift 1929209
  have htrace : WordTrace (prefixWord ++ tailWord_1929209) baseStart_1929209 baseEnd_1929209 := by
    simpa [prefixWord, tailWord_1929209, baseEnd_1929209] using wordTrace_append hprefix tailTrace_1929209
  have hstable : (prefixWord ++ tailWord_1929209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929209).length < 2 ^ (prefixWord ++ tailWord_1929209).sum := by decide
  have hdescent : baseEnd_1929209 < baseStart_1929209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929235 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 3, 4]
def baseStart_1929235 : Nat := 118140960795 + 1929235 * 2 ^ 59
def prefixEnd_1929235 : Nat := 4983230072969 + 3 ^ 40 * 1929235 * 2
def baseEnd_1929235 : Nat := 660416566984576395260077

theorem tailTrace_1929235 : CollatzResearch.WordTrace tailWord_1929235 prefixEnd_1929235 660416566984576395260077 := by
  unfold tailWord_1929235
  simp only [CollatzResearch.WordTrace]
  refine ⟨70364981165718556951301159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46909987443812371300867439 70364981165718556951301159)
  ·
    refine ⟨105547471748577835426951739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70364981165718556951301159 105547471748577835426951739)
    ·
      refine ⟨158321207622866753140427609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105547471748577835426951739 158321207622866753140427609)
      ·
        refine ⟨118740905717150064855320707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158321207622866753140427609 118740905717150064855320707)
        ·
          refine ⟨178111358575725097282981061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118740905717150064855320707 178111358575725097282981061)
          ·
            refine ⟨33395879732948455740558949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178111358575725097282981061 33395879732948455740558949)
            ·
              refine ⟨6261727449927835451354803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33395879732948455740558949 6261727449927835451354803)
              ·
                refine ⟨9392591174891753177032205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261727449927835451354803 9392591174891753177032205)
                ·
                  refine ⟨3522221690584407441387077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9392591174891753177032205 3522221690584407441387077)
                  ·
                    refine ⟨660416566984576395260077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522221690584407441387077 660416566984576395260077)
                    ·
                      rfl

theorem cell22_1929235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_1929235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929235 prefixEnd_1929235 := by exact prefixLift 1929235
  have htrace : WordTrace (prefixWord ++ tailWord_1929235) baseStart_1929235 baseEnd_1929235 := by
    simpa [prefixWord, tailWord_1929235, baseEnd_1929235] using wordTrace_append hprefix tailTrace_1929235
  have hstable : (prefixWord ++ tailWord_1929235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929235).length < 2 ^ (prefixWord ++ tailWord_1929235).sum := by decide
  have hdescent : baseEnd_1929235 < baseStart_1929235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929250 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1929250 : Nat := 118140960795 + 1929250 * 2 ^ 59
def prefixEnd_1929250 : Nat := 4983230072969 + 3 ^ 40 * 1929250 * 2
def baseEnd_1929250 : Nat := 220140567263707118711677

theorem tailTrace_1929250 : CollatzResearch.WordTrace tailWord_1929250 prefixEnd_1929250 220140567263707118711677 := by
  unfold tailWord_1929250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17591382065166053628274301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46910352173776143008731469 17591382065166053628274301)
  ·
    refine ⟨6596768274437270110602863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17591382065166053628274301 6596768274437270110602863)
    ·
      refine ⟨9895152411655905165904295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596768274437270110602863 9895152411655905165904295)
      ·
        refine ⟨14842728617483857748856443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9895152411655905165904295 14842728617483857748856443)
        ·
          refine ⟨22264092926225786623284665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14842728617483857748856443 22264092926225786623284665)
          ·
            refine ⟨16698069694669339967463499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22264092926225786623284665 16698069694669339967463499)
            ·
              refine ⟨25047104542004009951195249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16698069694669339967463499 25047104542004009951195249)
              ·
                refine ⟨18785328406503007463396437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25047104542004009951195249 18785328406503007463396437)
                ·
                  refine ⟨220140567263707118711677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18785328406503007463396437 220140567263707118711677)
                  ·
                    rfl

theorem cell22_1929250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1929250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929250 prefixEnd_1929250 := by exact prefixLift 1929250
  have htrace : WordTrace (prefixWord ++ tailWord_1929250) baseStart_1929250 baseEnd_1929250 := by
    simpa [prefixWord, tailWord_1929250, baseEnd_1929250] using wordTrace_append hprefix tailTrace_1929250
  have hstable : (prefixWord ++ tailWord_1929250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929250).length < 2 ^ (prefixWord ++ tailWord_1929250).sum := by decide
  have hdescent : baseEnd_1929250 < baseStart_1929250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929256 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 5]
def baseStart_1929256 : Nat := 118140960795 + 1929256 * 2 ^ 59
def prefixEnd_1929256 : Nat := 4983230072969 + 3 ^ 40 * 1929256 * 2
def baseEnd_1929256 : Nat := 220141251904579780161671

theorem tailTrace_1929256 : CollatzResearch.WordTrace tailWord_1929256 prefixEnd_1929256 220141251904579780161671 := by
  unfold tailWord_1929256
  simp only [CollatzResearch.WordTrace]
  refine ⟨35182873549321238768907811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46910498065761651691877081 35182873549321238768907811)
  ·
    refine ⟨52774310323981858153361717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35182873549321238768907811 52774310323981858153361717)
    ·
      refine ⟨4947591592873299201877661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52774310323981858153361717 4947591592873299201877661)
      ·
        refine ⟨1855346847327487200704123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4947591592873299201877661 1855346847327487200704123)
        ·
          refine ⟨2783020270991230801056185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855346847327487200704123 2783020270991230801056185)
          ·
            refine ⟨2087265203243423100792139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783020270991230801056185 2087265203243423100792139)
            ·
              refine ⟨3130897804865134651188209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087265203243423100792139 3130897804865134651188209)
              ·
                refine ⟨2348173353648850988391157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130897804865134651188209 2348173353648850988391157)
                ·
                  refine ⟨220141251904579780161671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2348173353648850988391157 220141251904579780161671)
                  ·
                    rfl

theorem cell22_1929256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_1929256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929256 prefixEnd_1929256 := by exact prefixLift 1929256
  have htrace : WordTrace (prefixWord ++ tailWord_1929256) baseStart_1929256 baseEnd_1929256 := by
    simpa [prefixWord, tailWord_1929256, baseEnd_1929256] using wordTrace_append hprefix tailTrace_1929256
  have hstable : (prefixWord ++ tailWord_1929256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929256).length < 2 ^ (prefixWord ++ tailWord_1929256).sum := by decide
  have hdescent : baseEnd_1929256 < baseStart_1929256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929267 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 4]
def baseStart_1929267 : Nat := 118140960795 + 1929267 * 2 ^ 59
def prefixEnd_1929267 : Nat := 4983230072969 + 3 ^ 40 * 1929267 * 2
def baseEnd_1929267 : Nat := 220142507079512992819993

theorem tailTrace_1929267 : CollatzResearch.WordTrace tailWord_1929267 prefixEnd_1929267 220142507079512992819993 := by
  unfold tailWord_1929267
  simp only [CollatzResearch.WordTrace]
  refine ⟨70366148301602626416466055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46910765534401750944310703 70366148301602626416466055)
  ·
    refine ⟨105549222452403939624699083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70366148301602626416466055 105549222452403939624699083)
    ·
      refine ⟨158323833678605909437048625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105549222452403939624699083 158323833678605909437048625)
      ·
        refine ⟨118742875258954432077786469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158323833678605909437048625 118742875258954432077786469)
        ·
          refine ⟨22264289111053956014584963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118742875258954432077786469 22264289111053956014584963)
          ·
            refine ⟨33396433666580934021877445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22264289111053956014584963 33396433666580934021877445)
            ·
              refine ⟨6261831312483925129102021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33396433666580934021877445 6261831312483925129102021)
              ·
                refine ⟨1174093371090735961706629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6261831312483925129102021 1174093371090735961706629)
                ·
                  refine ⟨220142507079512992819993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174093371090735961706629 220142507079512992819993)
                  ·
                    rfl

theorem cell22_1929267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 4].length) (baseStart_1929267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929267 prefixEnd_1929267 := by exact prefixLift 1929267
  have htrace : WordTrace (prefixWord ++ tailWord_1929267) baseStart_1929267 baseEnd_1929267 := by
    simpa [prefixWord, tailWord_1929267, baseEnd_1929267] using wordTrace_append hprefix tailTrace_1929267
  have hstable : (prefixWord ++ tailWord_1929267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929267).length < 2 ^ (prefixWord ++ tailWord_1929267).sum := by decide
  have hdescent : baseEnd_1929267 < baseStart_1929267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929280 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_1929280 : Nat := 118140960795 + 1929280 * 2 ^ 59
def prefixEnd_1929280 : Nat := 4983230072969 + 3 ^ 40 * 1929280 * 2
def baseEnd_1929280 : Nat := 660431971404211277884939

theorem tailTrace_1929280 : CollatzResearch.WordTrace tailWord_1929280 prefixEnd_1929280 660431971404211277884939 := by
  unfold tailWord_1929280
  simp only [CollatzResearch.WordTrace]
  refine ⟨35183311225277764818344647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46911081633703686424459529 35183311225277764818344647)
  ·
    refine ⟨52774966837916647227516971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35183311225277764818344647 52774966837916647227516971)
    ·
      refine ⟨79162450256874970841275457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52774966837916647227516971 79162450256874970841275457)
      ·
        refine ⟨59371837692656228130956593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79162450256874970841275457 59371837692656228130956593)
        ·
          refine ⟨44528878269492171098217445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59371837692656228130956593 44528878269492171098217445)
          ·
            refine ⟨8349164675529782080915771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44528878269492171098217445 8349164675529782080915771)
            ·
              refine ⟨12523747013294673121373657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8349164675529782080915771 12523747013294673121373657)
              ·
                refine ⟨9392810259971004841030243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12523747013294673121373657 9392810259971004841030243)
                ·
                  refine ⟨14089215389956507261545365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9392810259971004841030243 14089215389956507261545365)
                  ·
                    refine ⟨660431971404211277884939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14089215389956507261545365 660431971404211277884939)
                    ·
                      rfl

theorem cell22_1929280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_1929280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929280 prefixEnd_1929280 := by exact prefixLift 1929280
  have htrace : WordTrace (prefixWord ++ tailWord_1929280) baseStart_1929280 baseEnd_1929280 := by
    simpa [prefixWord, tailWord_1929280, baseEnd_1929280] using wordTrace_append hprefix tailTrace_1929280
  have hstable : (prefixWord ++ tailWord_1929280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929280).length < 2 ^ (prefixWord ++ tailWord_1929280).sum := by decide
  have hdescent : baseEnd_1929280 < baseStart_1929280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929286 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1929286 : Nat := 118140960795 + 1929286 * 2 ^ 59
def prefixEnd_1929286 : Nat := 4983230072969 + 3 ^ 40 * 1929286 * 2
def baseEnd_1929286 : Nat := 660434025326829262234921

theorem tailTrace_1929286 : CollatzResearch.WordTrace tailWord_1929286 prefixEnd_1929286 660434025326829262234921 := by
  unfold tailWord_1929286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198963790266681020668991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46911227525689195107605141 2198963790266681020668991)
  ·
    refine ⟨3298445685400021531003487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2198963790266681020668991 3298445685400021531003487)
    ·
      refine ⟨4947668528100032296505231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298445685400021531003487 4947668528100032296505231)
      ·
        refine ⟨7421502792150048444757847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947668528100032296505231 7421502792150048444757847)
        ·
          refine ⟨11132254188225072667136771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421502792150048444757847 11132254188225072667136771)
          ·
            refine ⟨16698381282337609000705157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132254188225072667136771 16698381282337609000705157)
            ·
              refine ⟨3130946490438301687632217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16698381282337609000705157 3130946490438301687632217)
              ·
                refine ⟨2348209867828726265724163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130946490438301687632217 2348209867828726265724163)
                ·
                  refine ⟨3522314801743089398586245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348209867828726265724163 3522314801743089398586245)
                  ·
                    refine ⟨660434025326829262234921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522314801743089398586245 660434025326829262234921)
                    ·
                      rfl

theorem cell22_1929286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1929286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929286 prefixEnd_1929286 := by exact prefixLift 1929286
  have htrace : WordTrace (prefixWord ++ tailWord_1929286) baseStart_1929286 baseEnd_1929286 := by
    simpa [prefixWord, tailWord_1929286, baseEnd_1929286] using wordTrace_append hprefix tailTrace_1929286
  have hstable : (prefixWord ++ tailWord_1929286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929286).length < 2 ^ (prefixWord ++ tailWord_1929286).sum := by decide
  have hdescent : baseEnd_1929286 < baseStart_1929286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929355 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_1929355 : Nat := 118140960795 + 1929355 * 2 ^ 59
def prefixEnd_1929355 : Nat := 4983230072969 + 3 ^ 40 * 1929355 * 2
def baseEnd_1929355 : Nat := 660457645436936082259709

theorem tailTrace_1929355 : CollatzResearch.WordTrace tailWord_1929355 prefixEnd_1929355 660457645436936082259709 := by
  unfold tailWord_1929355
  simp only [CollatzResearch.WordTrace]
  refine ⟨70369357925283817445669519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46912905283522544963779679 70369357925283817445669519)
  ·
    refine ⟨105554036887925726168504279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70369357925283817445669519 105554036887925726168504279)
    ·
      refine ⟨158331055331888589252756419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105554036887925726168504279 158331055331888589252756419)
      ·
        refine ⟨237496582997832883879134629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158331055331888589252756419 237496582997832883879134629)
        ·
          refine ⟨44530609312093665727337743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237496582997832883879134629 44530609312093665727337743)
          ·
            refine ⟨66795913968140498591006615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44530609312093665727337743 66795913968140498591006615)
            ·
              refine ⟨100193870952210747886509923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66795913968140498591006615 100193870952210747886509923)
              ·
                refine ⟨150290806428316121829764885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100193870952210747886509923 150290806428316121829764885)
                ·
                  refine ⟨7044881551327318210770229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150290806428316121829764885 7044881551327318210770229)
                  ·
                    refine ⟨660457645436936082259709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7044881551327318210770229 660457645436936082259709)
                    ·
                      rfl

theorem cell22_1929355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_1929355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929355 prefixEnd_1929355 := by exact prefixLift 1929355
  have htrace : WordTrace (prefixWord ++ tailWord_1929355) baseStart_1929355 baseEnd_1929355 := by
    simpa [prefixWord, tailWord_1929355, baseEnd_1929355] using wordTrace_append hprefix tailTrace_1929355
  have hstable : (prefixWord ++ tailWord_1929355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929355).length < 2 ^ (prefixWord ++ tailWord_1929355).sum := by decide
  have hdescent : baseEnd_1929355 < baseStart_1929355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929372 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1929372 : Nat := 118140960795 + 1929372 * 2 ^ 59
def prefixEnd_1929372 : Nat := 4983230072969 + 3 ^ 40 * 1929372 * 2
def baseEnd_1929372 : Nat := 660463464884353704584657

theorem tailTrace_1929372 : CollatzResearch.WordTrace tailWord_1929372 prefixEnd_1929372 660463464884353704584657 := by
  unfold tailWord_1929372
  simp only [CollatzResearch.WordTrace]
  refine ⟨35184988983111114674519185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46913318644148152899358913 35184988983111114674519185)
  ·
    refine ⟨26388741737333336005889389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35184988983111114674519185 26388741737333336005889389)
    ·
      refine ⟨9895778151500001002208521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26388741737333336005889389 9895778151500001002208521)
      ·
        refine ⟨7421833613625000751656391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9895778151500001002208521 7421833613625000751656391)
        ·
          refine ⟨11132750420437501127484587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421833613625000751656391 11132750420437501127484587)
          ·
            refine ⟨16699125630656251691226881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132750420437501127484587 16699125630656251691226881)
            ·
              refine ⟨12524344222992188768420161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16699125630656251691226881 12524344222992188768420161)
              ·
                refine ⟨9393258167244141576315121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12524344222992188768420161 9393258167244141576315121)
                ·
                  refine ⟨7044943625433106182236341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9393258167244141576315121 7044943625433106182236341)
                  ·
                    refine ⟨660463464884353704584657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7044943625433106182236341 660463464884353704584657)
                    ·
                      rfl

theorem cell22_1929372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1929372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929372 prefixEnd_1929372 := by exact prefixLift 1929372
  have htrace : WordTrace (prefixWord ++ tailWord_1929372) baseStart_1929372 baseEnd_1929372 := by
    simpa [prefixWord, tailWord_1929372, baseEnd_1929372] using wordTrace_append hprefix tailTrace_1929372
  have hstable : (prefixWord ++ tailWord_1929372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929372).length < 2 ^ (prefixWord ++ tailWord_1929372).sum := by decide
  have hdescent : baseEnd_1929372 < baseStart_1929372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929378 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1929378 : Nat := 118140960795 + 1929378 * 2 ^ 59
def prefixEnd_1929378 : Nat := 4983230072969 + 3 ^ 40 * 1929378 * 2
def baseEnd_1929378 : Nat := 660465518806971688934639

theorem tailTrace_1929378 : CollatzResearch.WordTrace tailWord_1929378 prefixEnd_1929378 660465518806971688934639 := by
  unfold tailWord_1929378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17592549201050123093439197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46913464536133661582504525 17592549201050123093439197)
  ·
    refine ⟨6597205950393796160039699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17592549201050123093439197 6597205950393796160039699)
    ·
      refine ⟨9895808925590694240059549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597205950393796160039699 9895808925590694240059549)
      ·
        refine ⟨3710928347096510340022331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9895808925590694240059549 3710928347096510340022331)
        ·
          refine ⟨5566392520644765510033497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710928347096510340022331 5566392520644765510033497)
          ·
            refine ⟨4174794390483574132525123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566392520644765510033497 4174794390483574132525123)
            ·
              refine ⟨6262191585725361198787685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174794390483574132525123 6262191585725361198787685)
              ·
                refine ⟨1174160922323505224772691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6262191585725361198787685 1174160922323505224772691)
                ·
                  refine ⟨1761241383485257837159037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174160922323505224772691 1761241383485257837159037)
                  ·
                    refine ⟨660465518806971688934639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761241383485257837159037 660465518806971688934639)
                    ·
                      rfl

theorem cell22_1929378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1929378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929378 prefixEnd_1929378 := by exact prefixLift 1929378
  have htrace : WordTrace (prefixWord ++ tailWord_1929378) baseStart_1929378 baseEnd_1929378 := by
    simpa [prefixWord, tailWord_1929378, baseEnd_1929378] using wordTrace_append hprefix tailTrace_1929378
  have hstable : (prefixWord ++ tailWord_1929378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929378).length < 2 ^ (prefixWord ++ tailWord_1929378).sum := by decide
  have hdescent : baseEnd_1929378 < baseStart_1929378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929389 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1929389 : Nat := 118140960795 + 1929389 * 2 ^ 59
def prefixEnd_1929389 : Nat := 4983230072969 + 3 ^ 40 * 1929389 * 2
def baseEnd_1929389 : Nat := 660469284331771326909605

theorem tailTrace_1929389 : CollatzResearch.WordTrace tailWord_1929389 prefixEnd_1929389 660469284331771326909605 := by
  unfold tailWord_1929389
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370598007160641252407221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46913732004773760834938147 70370598007160641252407221)
  ·
    refine ⟨6597243563171310117413177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70370598007160641252407221 6597243563171310117413177)
    ·
      refine ⟨4947932672378482588059883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6597243563171310117413177 4947932672378482588059883)
      ·
        refine ⟨7421899008567723882089825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947932672378482588059883 7421899008567723882089825)
        ·
          refine ⟨5566424256425792911567369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7421899008567723882089825 5566424256425792911567369)
          ·
            refine ⟨4174818192319344683675527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566424256425792911567369 4174818192319344683675527)
            ·
              refine ⟨6262227288479017025513291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174818192319344683675527 6262227288479017025513291)
              ·
                refine ⟨9393340932718525538269937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262227288479017025513291 9393340932718525538269937)
                ·
                  refine ⟨7045005699538894153702453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9393340932718525538269937 7045005699538894153702453)
                  ·
                    refine ⟨660469284331771326909605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7045005699538894153702453 660469284331771326909605)
                    ·
                      rfl

theorem cell22_1929389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1929389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929389 prefixEnd_1929389 := by exact prefixLift 1929389
  have htrace : WordTrace (prefixWord ++ tailWord_1929389) baseStart_1929389 baseEnd_1929389 := by
    simpa [prefixWord, tailWord_1929389, baseEnd_1929389] using wordTrace_append hprefix tailTrace_1929389
  have hstable : (prefixWord ++ tailWord_1929389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929389).length < 2 ^ (prefixWord ++ tailWord_1929389).sum := by decide
  have hdescent : baseEnd_1929389 < baseStart_1929389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929419 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 4]
def baseStart_1929419 : Nat := 118140960795 + 1929419 * 2 ^ 59
def prefixEnd_1929419 : Nat := 4983230072969 + 3 ^ 40 * 1929419 * 2
def baseEnd_1929419 : Nat := 220159851314953749553171

theorem tailTrace_1929419 : CollatzResearch.WordTrace tailWord_1929419 prefixEnd_1929419 220159851314953749553171 := by
  unfold tailWord_1929419
  simp only [CollatzResearch.WordTrace]
  refine ⟨70371692197051956375999311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46914461464701304250666207 70371692197051956375999311)
  ·
    refine ⟨105557538295577934563998967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70371692197051956375999311 105557538295577934563998967)
    ·
      refine ⟨158336307443366901845998451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105557538295577934563998967 158336307443366901845998451)
      ·
        refine ⟨237504461165050352768997677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158336307443366901845998451 237504461165050352768997677)
        ·
          refine ⟨89064172936893882288374129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237504461165050352768997677 89064172936893882288374129)
          ·
            refine ⟨66798129702670411716280597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89064172936893882288374129 66798129702670411716280597)
            ·
              refine ⟨3131162329812675549200653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66798129702670411716280597 3131162329812675549200653)
              ·
                refine ⟨1174185873679753330950245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3131162329812675549200653 1174185873679753330950245)
                ·
                  refine ⟨220159851314953749553171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174185873679753330950245 220159851314953749553171)
                  ·
                    rfl

theorem cell22_1929419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 4].length) (baseStart_1929419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929419 prefixEnd_1929419 := by exact prefixLift 1929419
  have htrace : WordTrace (prefixWord ++ tailWord_1929419) baseStart_1929419 baseEnd_1929419 := by
    simpa [prefixWord, tailWord_1929419, baseEnd_1929419] using wordTrace_append hprefix tailTrace_1929419
  have hstable : (prefixWord ++ tailWord_1929419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929419).length < 2 ^ (prefixWord ++ tailWord_1929419).sum := by decide
  have hdescent : baseEnd_1929419 < baseStart_1929419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929451 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 2, 3]
def baseStart_1929451 : Nat := 118140960795 + 1929451 * 2 ^ 59
def prefixEnd_1929451 : Nat := 4983230072969 + 3 ^ 40 * 1929451 * 2
def baseEnd_1929451 : Nat := 660490508198823831859415

theorem tailTrace_1929451 : CollatzResearch.WordTrace tailWord_1929451 prefixEnd_1929451 660490508198823831859415 := by
  unfold tailWord_1929451
  simp only [CollatzResearch.WordTrace]
  refine ⟨70372859332936025841164207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46915239555290683894109471 70372859332936025841164207)
  ·
    refine ⟨105559288999404038761746311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70372859332936025841164207 105559288999404038761746311)
    ·
      refine ⟨158338933499106058142619467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105559288999404038761746311 158338933499106058142619467)
      ·
        refine ⟨237508400248659087213929201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158338933499106058142619467 237508400248659087213929201)
        ·
          refine ⟨178131300186494315410446901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237508400248659087213929201 178131300186494315410446901)
          ·
            refine ⟨16699809392483842069729397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178131300186494315410446901 16699809392483842069729397)
            ·
              refine ⟨1565607130545360194037131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16699809392483842069729397 1565607130545360194037131)
              ·
                refine ⟨2348410695818040291055697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565607130545360194037131 2348410695818040291055697)
                ·
                  refine ⟨1761308021863530218291773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348410695818040291055697 1761308021863530218291773)
                  ·
                    refine ⟨660490508198823831859415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761308021863530218291773 660490508198823831859415)
                    ·
                      rfl

theorem cell22_1929451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 3].length) (baseStart_1929451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929451 prefixEnd_1929451 := by exact prefixLift 1929451
  have htrace : WordTrace (prefixWord ++ tailWord_1929451) baseStart_1929451 baseEnd_1929451 := by
    simpa [prefixWord, tailWord_1929451, baseEnd_1929451] using wordTrace_append hprefix tailTrace_1929451
  have hstable : (prefixWord ++ tailWord_1929451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929451).length < 2 ^ (prefixWord ++ tailWord_1929451).sum := by decide
  have hdescent : baseEnd_1929451 < baseStart_1929451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929502 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1929502 : Nat := 118140960795 + 1929502 * 2 ^ 59
def prefixEnd_1929502 : Nat := 4983230072969 + 3 ^ 40 * 1929502 * 2
def baseEnd_1929502 : Nat := 660507966541076698834259

theorem tailTrace_1929502 : CollatzResearch.WordTrace tailWord_1929502 prefixEnd_1929502 660507966541076698834259 := by
  unfold tailWord_1929502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796839931968907693908845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46916479637167507700847173 8796839931968907693908845)
  ·
    refine ⟨3298814974488340385215817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8796839931968907693908845 3298814974488340385215817)
    ·
      refine ⟨2474111230866255288911863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3298814974488340385215817 2474111230866255288911863)
      ·
        refine ⟨3711166846299382933367795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474111230866255288911863 3711166846299382933367795)
        ·
          refine ⟨5566750269449074400051693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711166846299382933367795 5566750269449074400051693)
          ·
            refine ⟨2087531351043402900019385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5566750269449074400051693 2087531351043402900019385)
            ·
              refine ⟨1565648513282552175014539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087531351043402900019385 1565648513282552175014539)
              ·
                refine ⟨2348472769923828262521809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565648513282552175014539 2348472769923828262521809)
                ·
                  refine ⟨1761354577442871196891357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348472769923828262521809 1761354577442871196891357)
                  ·
                    refine ⟨660507966541076698834259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761354577442871196891357 660507966541076698834259)
                    ·
                      rfl

theorem cell22_1929502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1929502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929502 prefixEnd_1929502 := by exact prefixLift 1929502
  have htrace : WordTrace (prefixWord ++ tailWord_1929502) baseStart_1929502 baseEnd_1929502 := by
    simpa [prefixWord, tailWord_1929502, baseEnd_1929502] using wordTrace_append hprefix tailTrace_1929502
  have hstable : (prefixWord ++ tailWord_1929502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929502).length < 2 ^ (prefixWord ++ tailWord_1929502).sum := by decide
  have hdescent : baseEnd_1929502 < baseStart_1929502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929507 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_1929507 : Nat := 118140960795 + 1929507 * 2 ^ 59
def prefixEnd_1929507 : Nat := 4983230072969 + 3 ^ 40 * 1929507 * 2
def baseEnd_1929507 : Nat := 660509678143258352459243

theorem tailTrace_1929507 : CollatzResearch.WordTrace tailWord_1929507 prefixEnd_1929507 660509678143258352459243 := by
  unfold tailWord_1929507
  simp only [CollatzResearch.WordTrace]
  refine ⟨70374901820733147405202775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46916601213822098270135183 70374901820733147405202775)
  ·
    refine ⟨105562352731099721107804163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70374901820733147405202775 105562352731099721107804163)
    ·
      refine ⟨158343529096649581661706245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105562352731099721107804163 158343529096649581661706245)
      ·
        refine ⟨29689411705621796561569921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158343529096649581661706245 29689411705621796561569921)
        ·
          refine ⟨22267058779216347421177441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29689411705621796561569921 22267058779216347421177441)
          ·
            refine ⟨16700294084412260565883081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22267058779216347421177441 16700294084412260565883081)
            ·
              refine ⟨12525220563309195424412311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16700294084412260565883081 12525220563309195424412311)
              ·
                refine ⟨18787830844963793136618467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525220563309195424412311 18787830844963793136618467)
                ·
                  refine ⟨28181746267445689704927701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18787830844963793136618467 28181746267445689704927701)
                  ·
                    refine ⟨660509678143258352459243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28181746267445689704927701 660509678143258352459243)
                    ·
                      rfl

theorem cell22_1929507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_1929507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929507 prefixEnd_1929507 := by exact prefixLift 1929507
  have htrace : WordTrace (prefixWord ++ tailWord_1929507) baseStart_1929507 baseEnd_1929507 := by
    simpa [prefixWord, tailWord_1929507, baseEnd_1929507] using wordTrace_append hprefix tailTrace_1929507
  have hstable : (prefixWord ++ tailWord_1929507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929507).length < 2 ^ (prefixWord ++ tailWord_1929507).sum := by decide
  have hdescent : baseEnd_1929507 < baseStart_1929507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929539 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 1, 4]
def baseStart_1929539 : Nat := 118140960795 + 1929539 * 2 ^ 59
def prefixEnd_1929539 : Nat := 4983230072969 + 3 ^ 40 * 1929539 * 2
def baseEnd_1929539 : Nat := 660520632397220935659145

theorem tailTrace_1929539 : CollatzResearch.WordTrace tailWord_1929539 prefixEnd_1929539 660520632397220935659145 := by
  unfold tailWord_1929539
  simp only [CollatzResearch.WordTrace]
  refine ⟨70376068956617216870367671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46917379304411477913578447 70376068956617216870367671)
  ·
    refine ⟨105564103434925825305551507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70376068956617216870367671 105564103434925825305551507)
    ·
      refine ⟨158346155152388737958327261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105564103434925825305551507 158346155152388737958327261)
      ·
        refine ⟨59379808182145776734372723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158346155152388737958327261 59379808182145776734372723)
        ·
          refine ⟨89069712273218665101559085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59379808182145776734372723 89069712273218665101559085)
          ·
            refine ⟨33401142102456999413084657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89069712273218665101559085 33401142102456999413084657)
            ·
              refine ⟨25050856576842749559813493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33401142102456999413084657 25050856576842749559813493)
              ·
                refine ⟨2348517804079007771232515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25050856576842749559813493 2348517804079007771232515)
                ·
                  refine ⟨3522776706118511656848773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348517804079007771232515 3522776706118511656848773)
                  ·
                    refine ⟨660520632397220935659145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522776706118511656848773 660520632397220935659145)
                    ·
                      rfl

theorem cell22_1929539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4].length) (baseStart_1929539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929539 prefixEnd_1929539 := by exact prefixLift 1929539
  have htrace : WordTrace (prefixWord ++ tailWord_1929539) baseStart_1929539 baseEnd_1929539 := by
    simpa [prefixWord, tailWord_1929539, baseEnd_1929539] using wordTrace_append hprefix tailTrace_1929539
  have hstable : (prefixWord ++ tailWord_1929539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929539).length < 2 ^ (prefixWord ++ tailWord_1929539).sum := by decide
  have hdescent : baseEnd_1929539 < baseStart_1929539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929569 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1929569 : Nat := 118140960795 + 1929569 * 2 ^ 59
def prefixEnd_1929569 : Nat := 4983230072969 + 3 ^ 40 * 1929569 * 2
def baseEnd_1929569 : Nat := 660530902010310857409053

theorem tailTrace_1929569 : CollatzResearch.WordTrace tailWord_1929569 prefixEnd_1929569 660530902010310857409053 := by
  unfold tailWord_1929569
  simp only [CollatzResearch.WordTrace]
  refine ⟨70377163146508531993959761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46918108764339021329306507 70377163146508531993959761)
  ·
    refine ⟨52782872359881398995469821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70377163146508531993959761 52782872359881398995469821)
    ·
      refine ⟨19793577134955524623301183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52782872359881398995469821 19793577134955524623301183)
      ·
        refine ⟨29690365702433286934951775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19793577134955524623301183 29690365702433286934951775)
        ·
          refine ⟨44535548553649930402427663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29690365702433286934951775 44535548553649930402427663)
          ·
            refine ⟨66803322830474895603641495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44535548553649930402427663 66803322830474895603641495)
            ·
              refine ⟨100204984245712343405462243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66803322830474895603641495 100204984245712343405462243)
              ·
                refine ⟨150307476368568515108193365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100204984245712343405462243 150307476368568515108193365)
                ·
                  refine ⟨1761415738694162286424141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 150307476368568515108193365 1761415738694162286424141)
                  ·
                    refine ⟨660530902010310857409053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761415738694162286424141 660530902010310857409053)
                    ·
                      rfl

theorem cell22_1929569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1929569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929569 prefixEnd_1929569 := by exact prefixLift 1929569
  have htrace : WordTrace (prefixWord ++ tailWord_1929569) baseStart_1929569 baseEnd_1929569 := by
    simpa [prefixWord, tailWord_1929569, baseEnd_1929569] using wordTrace_append hprefix tailTrace_1929569
  have hstable : (prefixWord ++ tailWord_1929569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929569).length < 2 ^ (prefixWord ++ tailWord_1929569).sum := by decide
  have hdescent : baseEnd_1929569 < baseStart_1929569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929584 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_1929584 : Nat := 118140960795 + 1929584 * 2 ^ 59
def prefixEnd_1929584 : Nat := 4983230072969 + 3 ^ 40 * 1929584 * 2
def baseEnd_1929584 : Nat := 660536036816855818284007

theorem tailTrace_1929584 : CollatzResearch.WordTrace tailWord_1929584 prefixEnd_1929584 660536036816855818284007 := by
  unfold tailWord_1929584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35188855120727094777877903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46918473494302793037170537 35188855120727094777877903)
  ·
    refine ⟨52783282681090642166816855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35188855120727094777877903 52783282681090642166816855)
    ·
      refine ⟨79174924021635963250225283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52783282681090642166816855 79174924021635963250225283)
      ·
        refine ⟨118762386032453944875337925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79174924021635963250225283 118762386032453944875337925)
        ·
          refine ⟨22267947381085114664125861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118762386032453944875337925 22267947381085114664125861)
          ·
            refine ⟨4175240133953458999523599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22267947381085114664125861 4175240133953458999523599)
            ·
              refine ⟨6262860200930188499285399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175240133953458999523599 6262860200930188499285399)
              ·
                refine ⟨9394290301395282748928099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262860200930188499285399 9394290301395282748928099)
                ·
                  refine ⟨14091435452092924123392149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394290301395282748928099 14091435452092924123392149)
                  ·
                    refine ⟨660536036816855818284007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14091435452092924123392149 660536036816855818284007)
                    ·
                      rfl

theorem cell22_1929584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_1929584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929584 prefixEnd_1929584 := by exact prefixLift 1929584
  have htrace : WordTrace (prefixWord ++ tailWord_1929584) baseStart_1929584 baseEnd_1929584 := by
    simpa [prefixWord, tailWord_1929584, baseEnd_1929584] using wordTrace_append hprefix tailTrace_1929584
  have hstable : (prefixWord ++ tailWord_1929584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929584).length < 2 ^ (prefixWord ++ tailWord_1929584).sum := by decide
  have hdescent : baseEnd_1929584 < baseStart_1929584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929590 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1929590 : Nat := 118140960795 + 1929590 * 2 ^ 59
def prefixEnd_1929590 : Nat := 4983230072969 + 3 ^ 40 * 1929590 * 2
def baseEnd_1929590 : Nat := 660538090739473802633989

theorem tailTrace_1929590 : CollatzResearch.WordTrace tailWord_1929590 prefixEnd_1929590 660538090739473802633989 := by
  unfold tailWord_1929590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398620567464528286279639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46918619386288301720316149 4398620567464528286279639)
  ·
    refine ⟨6597930851196792429419459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4398620567464528286279639 6597930851196792429419459)
    ·
      refine ⟨9896896276795188644129189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597930851196792429419459 9896896276795188644129189)
      ·
        refine ⟨1855668051899097870774223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9896896276795188644129189 1855668051899097870774223)
        ·
          refine ⟨2783502077848646806161335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855668051899097870774223 2783502077848646806161335)
          ·
            refine ⟨4175253116772970209242003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783502077848646806161335 4175253116772970209242003)
            ·
              refine ⟨6262879675159455313863005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175253116772970209242003 6262879675159455313863005)
              ·
                refine ⟨2348579878184795742698627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6262879675159455313863005 2348579878184795742698627)
                ·
                  refine ⟨3522869817277193614047941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348579878184795742698627 3522869817277193614047941)
                  ·
                    refine ⟨660538090739473802633989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522869817277193614047941 660538090739473802633989)
                    ·
                      rfl

theorem cell22_1929590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1929590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929590 prefixEnd_1929590 := by exact prefixLift 1929590
  have htrace : WordTrace (prefixWord ++ tailWord_1929590) baseStart_1929590 baseEnd_1929590 := by
    simpa [prefixWord, tailWord_1929590, baseEnd_1929590] using wordTrace_append hprefix tailTrace_1929590
  have hstable : (prefixWord ++ tailWord_1929590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929590).length < 2 ^ (prefixWord ++ tailWord_1929590).sum := by decide
  have hdescent : baseEnd_1929590 < baseStart_1929590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929620 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1929620 : Nat := 118140960795 + 1929620 * 2 ^ 59
def prefixEnd_1929620 : Nat := 4983230072969 + 3 ^ 40 * 1929620 * 2
def baseEnd_1929620 : Nat := 660548360352563724383897

theorem tailTrace_1929620 : CollatzResearch.WordTrace tailWord_1929620 prefixEnd_1929620 660548360352563724383897 := by
  unfold tailWord_1929620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35189511634661883852033157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46919348846215845136044209 35189511634661883852033157)
  ·
    refine ⟨6598033431499103222256217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35189511634661883852033157 6598033431499103222256217)
    ·
      refine ⟨4948525073624327416692163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6598033431499103222256217 4948525073624327416692163)
      ·
        refine ⟨7422787610436491125038245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948525073624327416692163 7422787610436491125038245)
        ·
          refine ⟨1391772676956842085944671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7422787610436491125038245 1391772676956842085944671)
          ·
            refine ⟨2087659015435263128917007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391772676956842085944671 2087659015435263128917007)
            ·
              refine ⟨3131488523152894693375511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087659015435263128917007 3131488523152894693375511)
              ·
                refine ⟨4697232784729342040063267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131488523152894693375511 4697232784729342040063267)
                ·
                  refine ⟨7045849177094013060094901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697232784729342040063267 7045849177094013060094901)
                  ·
                    refine ⟨660548360352563724383897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7045849177094013060094901 660548360352563724383897)
                    ·
                      rfl

theorem cell22_1929620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1929620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929620 prefixEnd_1929620 := by exact prefixLift 1929620
  have htrace : WordTrace (prefixWord ++ tailWord_1929620) baseStart_1929620 baseEnd_1929620 := by
    simpa [prefixWord, tailWord_1929620, baseEnd_1929620] using wordTrace_append hprefix tailTrace_1929620
  have hstable : (prefixWord ++ tailWord_1929620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929620).length < 2 ^ (prefixWord ++ tailWord_1929620).sum := by decide
  have hdescent : baseEnd_1929620 < baseStart_1929620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929631 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 3, 3]
def baseStart_1929631 : Nat := 118140960795 + 1929631 * 2 ^ 59
def prefixEnd_1929631 : Nat := 4983230072969 + 3 ^ 40 * 1929631 * 2
def baseEnd_1929631 : Nat := 660552125877363362358863

theorem tailTrace_1929631 : CollatzResearch.WordTrace tailWord_1929631 prefixEnd_1929631 660552125877363362358863 := by
  unfold tailWord_1929631
  simp only [CollatzResearch.WordTrace]
  refine ⟨70379424472283916582716747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46919616314855944388477831 70379424472283916582716747)
  ·
    refine ⟨105569136708425874874075121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70379424472283916582716747 105569136708425874874075121)
    ·
      refine ⟨79176852531319406155556341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105569136708425874874075121 79176852531319406155556341)
      ·
        refine ⟨7422829924811194327083407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79176852531319406155556341 7422829924811194327083407)
        ·
          refine ⟨11134244887216791490625111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7422829924811194327083407 11134244887216791490625111)
          ·
            refine ⟨16701367330825187235937667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134244887216791490625111 16701367330825187235937667)
            ·
              refine ⟨25052050996237780853906501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16701367330825187235937667 25052050996237780853906501)
              ·
                refine ⟨4697259561794583910107469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25052050996237780853906501 4697259561794583910107469)
                ·
                  refine ⟨1761472335672968966290301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4697259561794583910107469 1761472335672968966290301)
                  ·
                    refine ⟨660552125877363362358863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761472335672968966290301 660552125877363362358863)
                    ·
                      rfl

theorem cell22_1929631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_1929631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929631 prefixEnd_1929631 := by exact prefixLift 1929631
  have htrace : WordTrace (prefixWord ++ tailWord_1929631) baseStart_1929631 baseEnd_1929631 := by
    simpa [prefixWord, tailWord_1929631, baseEnd_1929631] using wordTrace_append hprefix tailTrace_1929631
  have hstable : (prefixWord ++ tailWord_1929631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929631).length < 2 ^ (prefixWord ++ tailWord_1929631).sum := by decide
  have hdescent : baseEnd_1929631 < baseStart_1929631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929689 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 8]
def baseStart_1929689 : Nat := 118140960795 + 1929689 * 2 ^ 59
def prefixEnd_1929689 : Nat := 4983230072969 + 3 ^ 40 * 1929689 * 2
def baseEnd_1929689 : Nat := 220190660154223514802895

theorem tailTrace_1929689 : CollatzResearch.WordTrace tailWord_1929689 prefixEnd_1929689 220190660154223514802895 := by
  unfold tailWord_1929689
  simp only [CollatzResearch.WordTrace]
  refine ⟨70381539906073792488328121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46921026604049194992218747 70381539906073792488328121)
  ·
    refine ⟨52786154929555344366246091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70381539906073792488328121 52786154929555344366246091)
    ·
      refine ⟨79179232394333016549369137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52786154929555344366246091 79179232394333016549369137)
      ·
        refine ⟨59384424295749762412026853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79179232394333016549369137 59384424295749762412026853)
        ·
          refine ⟨11134579555453080452255035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59384424295749762412026853 11134579555453080452255035)
          ·
            refine ⟨16701869333179620678382553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134579555453080452255035 16701869333179620678382553)
            ·
              refine ⟨12526401999884715508786915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16701869333179620678382553 12526401999884715508786915)
              ·
                refine ⟨18789602999827073263180373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12526401999884715508786915 18789602999827073263180373)
                ·
                  refine ⟨220190660154223514802895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18789602999827073263180373 220190660154223514802895)
                  ·
                    rfl

theorem cell22_1929689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_1929689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929689 prefixEnd_1929689 := by exact prefixLift 1929689
  have htrace : WordTrace (prefixWord ++ tailWord_1929689) baseStart_1929689 baseEnd_1929689 := by
    simpa [prefixWord, tailWord_1929689, baseEnd_1929689] using wordTrace_append hprefix tailTrace_1929689
  have hstable : (prefixWord ++ tailWord_1929689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929689).length < 2 ^ (prefixWord ++ tailWord_1929689).sum := by decide
  have hdescent : baseEnd_1929689 < baseStart_1929689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929708 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_1929708 : Nat := 118140960795 + 1929708 * 2 ^ 59
def prefixEnd_1929708 : Nat := 4983230072969 + 3 ^ 40 * 1929708 * 2
def baseEnd_1929708 : Nat := 660578484550960828183627

theorem tailTrace_1929708 : CollatzResearch.WordTrace tailWord_1929708 prefixEnd_1929708 660578484550960828183627 := by
  unfold tailWord_1929708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35191116446502479366634889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46921488595336639155513185 35191116446502479366634889)
  ·
    refine ⟨26393337334876859524976167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35191116446502479366634889 26393337334876859524976167)
    ·
      refine ⟨39590006002315289287464251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26393337334876859524976167 39590006002315289287464251)
      ·
        refine ⟨59385009003472933931196377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39590006002315289287464251 59385009003472933931196377)
        ·
          refine ⟨44538756752604700448397283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59385009003472933931196377 44538756752604700448397283)
          ·
            refine ⟨66808135128907050672595925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44538756752604700448397283 66808135128907050672595925)
            ·
              refine ⟨1565815667083759000138967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66808135128907050672595925 1565815667083759000138967)
              ·
                refine ⟨2348723500625638500208451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565815667083759000138967 2348723500625638500208451)
                ·
                  refine ⟨3523085250938457750312677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348723500625638500208451 3523085250938457750312677)
                  ·
                    refine ⟨660578484550960828183627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523085250938457750312677 660578484550960828183627)
                    ·
                      rfl

theorem cell22_1929708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_1929708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929708 prefixEnd_1929708 := by exact prefixLift 1929708
  have htrace : WordTrace (prefixWord ++ tailWord_1929708) baseStart_1929708 baseEnd_1929708 := by
    simpa [prefixWord, tailWord_1929708, baseEnd_1929708] using wordTrace_append hprefix tailTrace_1929708
  have hstable : (prefixWord ++ tailWord_1929708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929708).length < 2 ^ (prefixWord ++ tailWord_1929708).sum := by decide
  have hdescent : baseEnd_1929708 < baseStart_1929708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929721 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_1929721 : Nat := 118140960795 + 1929721 * 2 ^ 59
def prefixEnd_1929721 : Nat := 4983230072969 + 3 ^ 40 * 1929721 * 2
def baseEnd_1929721 : Nat := 660582934716633127608587

theorem tailTrace_1929721 : CollatzResearch.WordTrace tailWord_1929721 prefixEnd_1929721 660582934716633127608587 := by
  unfold tailWord_1929721
  simp only [CollatzResearch.WordTrace]
  refine ⟨70382707041957861953493017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46921804694638574635662011 70382707041957861953493017)
  ·
    refine ⟨52787030281468396465119763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70382707041957861953493017 52787030281468396465119763)
    ·
      refine ⟨79180545422202594697679645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52787030281468396465119763 79180545422202594697679645)
      ·
        refine ⟨29692704533325973011629867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79180545422202594697679645 29692704533325973011629867)
        ·
          refine ⟨44539056799988959517444801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29692704533325973011629867 44539056799988959517444801)
          ·
            refine ⟨33404292599991719638083601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44539056799988959517444801 33404292599991719638083601)
            ·
              refine ⟨25053219449993789728562701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33404292599991719638083601 25053219449993789728562701)
              ·
                refine ⟨9394957293747671148211013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25053219449993789728562701 9394957293747671148211013)
                ·
                  refine ⟨1761554492577688340289565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9394957293747671148211013 1761554492577688340289565)
                  ·
                    refine ⟨660582934716633127608587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761554492577688340289565 660582934716633127608587)
                    ·
                      rfl

theorem cell22_1929721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_1929721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929721 prefixEnd_1929721 := by exact prefixLift 1929721
  have htrace : WordTrace (prefixWord ++ tailWord_1929721) baseStart_1929721 baseEnd_1929721 := by
    simpa [prefixWord, tailWord_1929721, baseEnd_1929721] using wordTrace_append hprefix tailTrace_1929721
  have hstable : (prefixWord ++ tailWord_1929721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929721).length < 2 ^ (prefixWord ++ tailWord_1929721).sum := by decide
  have hdescent : baseEnd_1929721 < baseStart_1929721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929738 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1929738 : Nat := 118140960795 + 1929738 * 2 ^ 59
def prefixEnd_1929738 : Nat := 4983230072969 + 3 ^ 40 * 1929738 * 2
def baseEnd_1929738 : Nat := 660588754164050749933535

theorem tailTrace_1929738 : CollatzResearch.WordTrace tailWord_1929738 prefixEnd_1929738 660588754164050749933535 := by
  unfold tailWord_1929738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17595831770724068464215467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46922218055264182571241245 17595831770724068464215467)
  ·
    refine ⟨26393747656086102696323201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17595831770724068464215467 26393747656086102696323201)
    ·
      refine ⟨19795310742064577022242401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26393747656086102696323201 19795310742064577022242401)
      ·
        refine ⟨14846483056548432766681801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19795310742064577022242401 14846483056548432766681801)
        ·
          refine ⟨11134862292411324575011351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14846483056548432766681801 11134862292411324575011351)
          ·
            refine ⟨16702293438616986862517027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134862292411324575011351 16702293438616986862517027)
            ·
              refine ⟨25053440157925480293775541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16702293438616986862517027 25053440157925480293775541)
              ·
                refine ⟨2348760014805513777541457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25053440157925480293775541 2348760014805513777541457)
                ·
                  refine ⟨1761570011104135333156093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348760014805513777541457 1761570011104135333156093)
                  ·
                    refine ⟨660588754164050749933535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761570011104135333156093 660588754164050749933535)
                    ·
                      rfl

theorem cell22_1929738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1929738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929738 prefixEnd_1929738 := by exact prefixLift 1929738
  have htrace : WordTrace (prefixWord ++ tailWord_1929738) baseStart_1929738 baseEnd_1929738 := by
    simpa [prefixWord, tailWord_1929738, baseEnd_1929738] using wordTrace_append hprefix tailTrace_1929738
  have hstable : (prefixWord ++ tailWord_1929738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929738).length < 2 ^ (prefixWord ++ tailWord_1929738).sum := by decide
  have hdescent : baseEnd_1929738 < baseStart_1929738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929783 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 3, 3]
def baseStart_1929783 : Nat := 118140960795 + 1929783 * 2 ^ 59
def prefixEnd_1929783 : Nat := 4983230072969 + 3 ^ 40 * 1929783 * 2
def baseEnd_1929783 : Nat := 660604158583685632558397

theorem tailTrace_1929783 : CollatzResearch.WordTrace tailWord_1929783 prefixEnd_1929783 660604158583685632558397 := by
  unfold tailWord_1929783
  simp only [CollatzResearch.WordTrace]
  refine ⟨70384968367733246542250003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46923312245155497694833335 70384968367733246542250003)
  ·
    refine ⟨105577452551599869813375005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70384968367733246542250003 105577452551599869813375005)
    ·
      refine ⟨39591544706849951180015627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105577452551599869813375005 39591544706849951180015627)
      ·
        refine ⟨59387317060274926770023441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39591544706849951180015627 59387317060274926770023441)
        ·
          refine ⟨44540487795206195077517581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59387317060274926770023441 44540487795206195077517581)
          ·
            refine ⟨16702682923202323154069093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44540487795206195077517581 16702682923202323154069093)
            ·
              refine ⟨3131753048100435591387955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16702682923202323154069093 3131753048100435591387955)
              ·
                refine ⟨4697629572150653387081933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131753048100435591387955 4697629572150653387081933)
                ·
                  refine ⟨1761611089556495020155725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4697629572150653387081933 1761611089556495020155725)
                  ·
                    refine ⟨660604158583685632558397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761611089556495020155725 660604158583685632558397)
                    ·
                      rfl

theorem cell22_1929783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_1929783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929783 prefixEnd_1929783 := by exact prefixLift 1929783
  have htrace : WordTrace (prefixWord ++ tailWord_1929783) baseStart_1929783 baseEnd_1929783 := by
    simpa [prefixWord, tailWord_1929783, baseEnd_1929783] using wordTrace_append hprefix tailTrace_1929783
  have hstable : (prefixWord ++ tailWord_1929783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929783).length < 2 ^ (prefixWord ++ tailWord_1929783).sum := by decide
  have hdescent : baseEnd_1929783 < baseStart_1929783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929860 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1929860 : Nat := 118140960795 + 1929860 * 2 ^ 59
def prefixEnd_1929860 : Nat := 4983230072969 + 3 ^ 40 * 1929860 * 2
def baseEnd_1929860 : Nat := 660630517257283098383161

theorem tailTrace_1929860 : CollatzResearch.WordTrace tailWord_1929860 prefixEnd_1929860 660630517257283098383161 := by
  unfold tailWord_1929860
  simp only [CollatzResearch.WordTrace]
  refine ⟨35193888394227144346401517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46925184525636192461868689 35193888394227144346401517)
  ·
    refine ⟨13197708147835179129900569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35193888394227144346401517 13197708147835179129900569)
    ·
      refine ⟨9898281110876384347425427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13197708147835179129900569 9898281110876384347425427)
      ·
        refine ⟨14847421666314576521138141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9898281110876384347425427 14847421666314576521138141)
        ·
          refine ⟨5567783124867966195426803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14847421666314576521138141 5567783124867966195426803)
          ·
            refine ⟨8351674687301949293140205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567783124867966195426803 8351674687301949293140205)
            ·
              refine ⟨3131878007738230984927577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8351674687301949293140205 3131878007738230984927577)
              ·
                refine ⟨2348908505803673238695683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131878007738230984927577 2348908505803673238695683)
                ·
                  refine ⟨3523362758705509858043525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348908505803673238695683 3523362758705509858043525)
                  ·
                    refine ⟨660630517257283098383161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523362758705509858043525 660630517257283098383161)
                    ·
                      rfl

theorem cell22_1929860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1929860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929860 prefixEnd_1929860 := by exact prefixLift 1929860
  have htrace : WordTrace (prefixWord ++ tailWord_1929860) baseStart_1929860 baseEnd_1929860 := by
    simpa [prefixWord, tailWord_1929860, baseEnd_1929860] using wordTrace_append hprefix tailTrace_1929860
  have hstable : (prefixWord ++ tailWord_1929860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929860).length < 2 ^ (prefixWord ++ tailWord_1929860).sum := by decide
  have hdescent : baseEnd_1929860 < baseStart_1929860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 6, 4]
def baseStart_1929871 : Nat := 118140960795 + 1929871 * 2 ^ 59
def prefixEnd_1929871 : Nat := 4983230072969 + 3 ^ 40 * 1929871 * 2
def baseEnd_1929871 : Nat := 660634282782082736358127

theorem tailTrace_1929871 : CollatzResearch.WordTrace tailWord_1929871 prefixEnd_1929871 660634282782082736358127 := by
  unfold tailWord_1929871
  simp only [CollatzResearch.WordTrace]
  refine ⟨70388177991414437571453467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46925451994276291714302311 70388177991414437571453467)
  ·
    refine ⟨105582266987121656357180201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70388177991414437571453467 105582266987121656357180201)
    ·
      refine ⟨79186700240341242267885151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105582266987121656357180201 79186700240341242267885151)
      ·
        refine ⟨118780050360511863401827727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79186700240341242267885151 118780050360511863401827727)
        ·
          refine ⟨178170075540767795102741591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118780050360511863401827727 178170075540767795102741591)
          ·
            refine ⟨267255113311151692654112387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178170075540767795102741591 267255113311151692654112387)
            ·
              refine ⟨400882669966727538981168581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267255113311151692654112387 400882669966727538981168581)
              ·
                refine ⟨75165500618761413558969109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400882669966727538981168581 75165500618761413558969109)
                ·
                  refine ⟨3523382841504441260576677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75165500618761413558969109 3523382841504441260576677)
                  ·
                    refine ⟨660634282782082736358127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523382841504441260576677 660634282782082736358127)
                    ·
                      rfl

theorem cell22_1929871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_1929871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929871 prefixEnd_1929871 := by exact prefixLift 1929871
  have htrace : WordTrace (prefixWord ++ tailWord_1929871) baseStart_1929871 baseEnd_1929871 := by
    simpa [prefixWord, tailWord_1929871, baseEnd_1929871] using wordTrace_append hprefix tailTrace_1929871
  have hstable : (prefixWord ++ tailWord_1929871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929871).length < 2 ^ (prefixWord ++ tailWord_1929871).sum := by decide
  have hdescent : baseEnd_1929871 < baseStart_1929871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929903 : List Nat := [1, 1, 2, 1, 2, 7, 1, 7]
def baseStart_1929903 : Nat := 118140960795 + 1929903 * 2 ^ 59
def prefixEnd_1929903 : Nat := 4983230072969 + 3 ^ 40 * 1929903 * 2
def baseEnd_1929903 : Nat := 73405026337338368839781

theorem tailTrace_1929903 : CollatzResearch.WordTrace tailWord_1929903 prefixEnd_1929903 73405026337338368839781 := by
  unfold tailWord_1929903
  simp only [CollatzResearch.WordTrace]
  refine ⟨70389345127298507036618363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46926230084865671357745575 70389345127298507036618363)
  ·
    refine ⟨105584017690947760554927545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70389345127298507036618363 105584017690947760554927545)
    ·
      refine ⟨79188013268210820416195659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105584017690947760554927545 79188013268210820416195659)
      ·
        refine ⟨118782019902316230624293489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79188013268210820416195659 118782019902316230624293489)
        ·
          refine ⟨89086514926737172968220117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118782019902316230624293489 89086514926737172968220117)
          ·
            refine ⟨2087965193595402491442659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 89086514926737172968220117 2087965193595402491442659)
            ·
              refine ⟨3131947790393103737163989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087965193595402491442659 3131947790393103737163989)
              ·
                refine ⟨73405026337338368839781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3131947790393103737163989 73405026337338368839781)
                ·
                  rfl

theorem cell22_1929903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 7].length) (baseStart_1929903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929903 prefixEnd_1929903 := by exact prefixLift 1929903
  have htrace : WordTrace (prefixWord ++ tailWord_1929903) baseStart_1929903 baseEnd_1929903 := by
    simpa [prefixWord, tailWord_1929903, baseEnd_1929903] using wordTrace_append hprefix tailTrace_1929903
  have hstable : (prefixWord ++ tailWord_1929903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929903).length < 2 ^ (prefixWord ++ tailWord_1929903).sum := by decide
  have hdescent : baseEnd_1929903 < baseStart_1929903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929926 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1929926 : Nat := 118140960795 + 1929926 * 2 ^ 59
def prefixEnd_1929926 : Nat := 4983230072969 + 3 ^ 40 * 1929926 * 2
def baseEnd_1929926 : Nat := 220217703468693642077653

theorem tailTrace_1929926 : CollatzResearch.WordTrace tailWord_1929926 prefixEnd_1929926 220217703468693642077653 := by
  unfold tailWord_1929926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199693250194224436397051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46926789337476787976470421 2199693250194224436397051)
  ·
    refine ⟨3299539875291336654595577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2199693250194224436397051 3299539875291336654595577)
    ·
      refine ⟨2474654906468502490946683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3299539875291336654595577 2474654906468502490946683)
      ·
        refine ⟨3711982359702753736420025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474654906468502490946683 3711982359702753736420025)
        ·
          refine ⟨2783986769777065302315019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3711982359702753736420025 2783986769777065302315019)
          ·
            refine ⟨4175980154665597953472529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783986769777065302315019 4175980154665597953472529)
            ·
              refine ⟨3131985115999198465104397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4175980154665597953472529 3131985115999198465104397)
              ·
                refine ⟨1174494418499699424414149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3131985115999198465104397 1174494418499699424414149)
                ·
                  refine ⟨220217703468693642077653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174494418499699424414149 220217703468693642077653)
                  ·
                    rfl

theorem cell22_1929926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1929926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929926 prefixEnd_1929926 := by exact prefixLift 1929926
  have htrace : WordTrace (prefixWord ++ tailWord_1929926) baseStart_1929926 baseEnd_1929926 := by
    simpa [prefixWord, tailWord_1929926, baseEnd_1929926] using wordTrace_append hprefix tailTrace_1929926
  have hstable : (prefixWord ++ tailWord_1929926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929926).length < 2 ^ (prefixWord ++ tailWord_1929926).sum := by decide
  have hdescent : baseEnd_1929926 < baseStart_1929926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929941 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_1929941 : Nat := 118140960795 + 1929941 * 2 ^ 59
def prefixEnd_1929941 : Nat := 4983230072969 + 3 ^ 40 * 1929941 * 2
def baseEnd_1929941 : Nat := 660658245212625887107913

theorem tailTrace_1929941 : CollatzResearch.WordTrace tailWord_1929941 prefixEnd_1929941 660658245212625887107913 := by
  unfold tailWord_1929941
  simp only [CollatzResearch.WordTrace]
  refine ⟨70390731101160839526501677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46927154067440559684334451 70390731101160839526501677)
  ·
    refine ⟨26396524162935314822438129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70390731101160839526501677 26396524162935314822438129)
    ·
      refine ⟨19797393122201486116828597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26396524162935314822438129 19797393122201486116828597)
      ·
        refine ⟨1856005605206389323452681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19797393122201486116828597 1856005605206389323452681)
        ·
          refine ⟨1392004203904791992589511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856005605206389323452681 1392004203904791992589511)
          ·
            refine ⟨2088006305857187988884267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392004203904791992589511 2088006305857187988884267)
            ·
              refine ⟨3132009458785781983326401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088006305857187988884267 3132009458785781983326401)
              ·
                refine ⟨2349007094089336487494801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132009458785781983326401 2349007094089336487494801)
                ·
                  refine ⟨1761755320567002365621101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349007094089336487494801 1761755320567002365621101)
                  ·
                    refine ⟨660658245212625887107913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761755320567002365621101 660658245212625887107913)
                    ·
                      rfl

theorem cell22_1929941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_1929941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929941 prefixEnd_1929941 := by exact prefixLift 1929941
  have htrace : WordTrace (prefixWord ++ tailWord_1929941) baseStart_1929941 baseEnd_1929941 := by
    simpa [prefixWord, tailWord_1929941, baseEnd_1929941] using wordTrace_append hprefix tailTrace_1929941
  have hstable : (prefixWord ++ tailWord_1929941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929941).length < 2 ^ (prefixWord ++ tailWord_1929941).sum := by decide
  have hdescent : baseEnd_1929941 < baseStart_1929941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929978 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1929978 : Nat := 118140960795 + 1929978 * 2 ^ 59
def prefixEnd_1929978 : Nat := 4983230072969 + 3 ^ 40 * 1929978 * 2
def baseEnd_1929978 : Nat := 660670911068770123932799

theorem tailTrace_1929978 : CollatzResearch.WordTrace tailWord_1929978 prefixEnd_1929978 660670911068770123932799 := by
  unfold tailWord_1929978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17598020150506698711399647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46928053734684529897065725 17598020150506698711399647)
  ·
    refine ⟨26397030225760048067099471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17598020150506698711399647 26397030225760048067099471)
    ·
      refine ⟨39595545338640072100649207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26397030225760048067099471 39595545338640072100649207)
      ·
        refine ⟨59393318007960108150973811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39595545338640072100649207 59393318007960108150973811)
        ·
          refine ⟨89089977011940162226460717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59393318007960108150973811 89089977011940162226460717)
          ·
            refine ⟨33408741379477560834922769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89089977011940162226460717 33408741379477560834922769)
            ·
              refine ⟨25056556034608170626192077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33408741379477560834922769 25056556034608170626192077)
              ·
                refine ⟨9396208512978063984822029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25056556034608170626192077 9396208512978063984822029)
                ·
                  refine ⟨3523578192366773994308261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9396208512978063984822029 3523578192366773994308261)
                  ·
                    refine ⟨660670911068770123932799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523578192366773994308261 660670911068770123932799)
                    ·
                      rfl

theorem cell22_1929978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1929978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929978 prefixEnd_1929978 := by exact prefixLift 1929978
  have htrace : WordTrace (prefixWord ++ tailWord_1929978) baseStart_1929978 baseEnd_1929978 := by
    simpa [prefixWord, tailWord_1929978, baseEnd_1929978] using wordTrace_append hprefix tailTrace_1929978
  have hstable : (prefixWord ++ tailWord_1929978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929978).length < 2 ^ (prefixWord ++ tailWord_1929978).sum := by decide
  have hdescent : baseEnd_1929978 < baseStart_1929978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929986 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1929986 : Nat := 118140960795 + 1929986 * 2 ^ 59
def prefixEnd_1929986 : Nat := 4983230072969 + 3 ^ 40 * 1929986 * 2
def baseEnd_1929986 : Nat := 660673649632260769732775

theorem tailTrace_1929986 : CollatzResearch.WordTrace tailWord_1929986 prefixEnd_1929986 660673649632260769732775 := by
  unfold tailWord_1929986
  simp only [CollatzResearch.WordTrace]
  refine ⟨17598093096499453052972453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46928248257331874807926541 17598093096499453052972453)
  ·
    refine ⟨3299642455593647447432335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17598093096499453052972453 3299642455593647447432335)
    ·
      refine ⟨4949463683390471171148503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299642455593647447432335 4949463683390471171148503)
      ·
        refine ⟨7424195525085706756722755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4949463683390471171148503 7424195525085706756722755)
        ·
          refine ⟨11136293287628560135084133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424195525085706756722755 11136293287628560135084133)
          ·
            refine ⟨2088054991430355025328275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11136293287628560135084133 2088054991430355025328275)
            ·
              refine ⟨3132082487145532537992413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088054991430355025328275 3132082487145532537992413)
              ·
                refine ⟨1174530932679574701747155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3132082487145532537992413 1174530932679574701747155)
                ·
                  refine ⟨1761796399019362052620733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174530932679574701747155 1761796399019362052620733)
                  ·
                    refine ⟨660673649632260769732775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761796399019362052620733 660673649632260769732775)
                    ·
                      rfl

theorem cell22_1929986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1929986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1929986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1929986 prefixEnd_1929986 := by exact prefixLift 1929986
  have htrace : WordTrace (prefixWord ++ tailWord_1929986) baseStart_1929986 baseEnd_1929986 := by
    simpa [prefixWord, tailWord_1929986, baseEnd_1929986] using wordTrace_append hprefix tailTrace_1929986
  have hstable : (prefixWord ++ tailWord_1929986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929986).length < 2 ^ (prefixWord ++ tailWord_1929986).sum := by decide
  have hdescent : baseEnd_1929986 < baseStart_1929986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930025 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_1930025 : Nat := 118140960795 + 1930025 * 2 ^ 59
def prefixEnd_1930025 : Nat := 4983230072969 + 3 ^ 40 * 1930025 * 2
def baseEnd_1930025 : Nat := 660687000129277668007655

theorem tailTrace_1930025 : CollatzResearch.WordTrace tailWord_1930025 prefixEnd_1930025 660687000129277668007655 := by
  unfold tailWord_1930025
  simp only [CollatzResearch.WordTrace]
  refine ⟨70393794832856521872559529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46929196555237681248373019 70393794832856521872559529)
  ·
    refine ⟨52795346124642391404419647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70393794832856521872559529 52795346124642391404419647)
    ·
      refine ⟨79193019186963587106629471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52795346124642391404419647 79193019186963587106629471)
      ·
        refine ⟨118789528780445380659944207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79193019186963587106629471 118789528780445380659944207)
        ·
          refine ⟨178184293170668070989916311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118789528780445380659944207 178184293170668070989916311)
          ·
            refine ⟨267276439756002106484874467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178184293170668070989916311 267276439756002106484874467)
            ·
              refine ⟨400914659634003159727311701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267276439756002106484874467 400914659634003159727311701)
              ·
                refine ⟨2349109333792987264027217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 400914659634003159727311701 2349109333792987264027217)
                ·
                  refine ⟨1761832000344740448020413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349109333792987264027217 1761832000344740448020413)
                  ·
                    refine ⟨660687000129277668007655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761832000344740448020413 660687000129277668007655)
                    ·
                      rfl

theorem cell22_1930025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_1930025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930025 prefixEnd_1930025 := by exact prefixLift 1930025
  have htrace : WordTrace (prefixWord ++ tailWord_1930025) baseStart_1930025 baseEnd_1930025 := by
    simpa [prefixWord, tailWord_1930025, baseEnd_1930025] using wordTrace_append hprefix tailTrace_1930025
  have hstable : (prefixWord ++ tailWord_1930025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930025).length < 2 ^ (prefixWord ++ tailWord_1930025).sum := by decide
  have hdescent : baseEnd_1930025 < baseStart_1930025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930029 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1930029 : Nat := 118140960795 + 1930029 * 2 ^ 59
def prefixEnd_1930029 : Nat := 4983230072969 + 3 ^ 40 * 1930029 * 2
def baseEnd_1930029 : Nat := 660688369411022990907643

theorem tailTrace_1930029 : CollatzResearch.WordTrace tailWord_1930029 prefixEnd_1930029 660688369411022990907643 := by
  unfold tailWord_1930029
  simp only [CollatzResearch.WordTrace]
  refine ⟨70393940724842030555705141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46929293816561353703803427 70393940724842030555705141)
  ·
    refine ⟨6599431942953940364597357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70393940724842030555705141 6599431942953940364597357)
    ·
      refine ⟨2474786978607727636724009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6599431942953940364597357 2474786978607727636724009)
      ·
        refine ⟨1856090233955795727543007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2474786978607727636724009 1856090233955795727543007)
        ·
          refine ⟨2784135350933693591314511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856090233955795727543007 2784135350933693591314511)
          ·
            refine ⟨4176203026400540386971767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784135350933693591314511 4176203026400540386971767)
            ·
              refine ⟨6264304539600810580457651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176203026400540386971767 6264304539600810580457651)
              ·
                refine ⟨9396456809401215870686477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264304539600810580457651 9396456809401215870686477)
                ·
                  refine ⟨3523671303525455951507429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9396456809401215870686477 3523671303525455951507429)
                  ·
                    refine ⟨660688369411022990907643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523671303525455951507429 660688369411022990907643)
                    ·
                      rfl

theorem cell22_1930029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1930029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930029 prefixEnd_1930029 := by exact prefixLift 1930029
  have htrace : WordTrace (prefixWord ++ tailWord_1930029) baseStart_1930029 baseEnd_1930029 := by
    simpa [prefixWord, tailWord_1930029, baseEnd_1930029] using wordTrace_append hprefix tailTrace_1930029
  have hstable : (prefixWord ++ tailWord_1930029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930029).length < 2 ^ (prefixWord ++ tailWord_1930029).sum := by decide
  have hdescent : baseEnd_1930029 < baseStart_1930029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930040 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_1930040 : Nat := 118140960795 + 1930040 * 2 ^ 59
def prefixEnd_1930040 : Nat := 4983230072969 + 3 ^ 40 * 1930040 * 2
def baseEnd_1930040 : Nat := 660692134935822628882609

theorem tailTrace_1930040 : CollatzResearch.WordTrace tailWord_1930040 prefixEnd_1930040 660692134935822628882609 := by
  unfold tailWord_1930040
  simp only [CollatzResearch.WordTrace]
  refine ⟨35197170963901089717177787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46929561285201452956237049 35197170963901089717177787)
  ·
    refine ⟨52795756445851634575766681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35197170963901089717177787 52795756445851634575766681)
    ·
      refine ⟨39596817334388725931825011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52795756445851634575766681 39596817334388725931825011)
      ·
        refine ⟨59395226001583088897737517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39596817334388725931825011 59395226001583088897737517)
        ·
          refine ⟨22273209750593658336651569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59395226001583088897737517 22273209750593658336651569)
          ·
            refine ⟨16704907312945243752488677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22273209750593658336651569 16704907312945243752488677)
            ·
              refine ⟨3132170121177233203591627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16704907312945243752488677 3132170121177233203591627)
              ·
                refine ⟨4698255181765849805387441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132170121177233203591627 4698255181765849805387441)
                ·
                  refine ⟨3523691386324387354040581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698255181765849805387441 3523691386324387354040581)
                  ·
                    refine ⟨660692134935822628882609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523691386324387354040581 660692134935822628882609)
                    ·
                      rfl

theorem cell22_1930040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_1930040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930040 prefixEnd_1930040 := by exact prefixLift 1930040
  have htrace : WordTrace (prefixWord ++ tailWord_1930040) baseStart_1930040 baseEnd_1930040 := by
    simpa [prefixWord, tailWord_1930040, baseEnd_1930040] using wordTrace_append hprefix tailTrace_1930040
  have hstable : (prefixWord ++ tailWord_1930040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930040).length < 2 ^ (prefixWord ++ tailWord_1930040).sum := by decide
  have hdescent : baseEnd_1930040 < baseStart_1930040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930087 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1930087 : Nat := 118140960795 + 1930087 * 2 ^ 59
def prefixEnd_1930087 : Nat := 4983230072969 + 3 ^ 40 * 1930087 * 2
def baseEnd_1930087 : Nat := 660708223996330172957465

theorem tailTrace_1930087 : CollatzResearch.WordTrace tailWord_1930087 prefixEnd_1930087 660708223996330172957465 := by
  unfold tailWord_1930087
  simp only [CollatzResearch.WordTrace]
  refine ⟨70396056158631906461316515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46930704105754604307544343 70396056158631906461316515)
  ·
    refine ⟨105594084237947859691974773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70396056158631906461316515 105594084237947859691974773)
    ·
      refine ⟨9899445397307611846122635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105594084237947859691974773 9899445397307611846122635)
      ·
        refine ⟨14849168095961417769183953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899445397307611846122635 14849168095961417769183953)
        ·
          refine ⟨11136876071971063326887965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14849168095961417769183953 11136876071971063326887965)
          ·
            refine ⟨4176328526989148747582987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11136876071971063326887965 4176328526989148747582987)
            ·
              refine ⟨6264492790483723121374481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176328526989148747582987 6264492790483723121374481)
              ·
                refine ⟨4698369592862792341030861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6264492790483723121374481 4698369592862792341030861)
                ·
                  refine ⟨1761888597323547127886573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4698369592862792341030861 1761888597323547127886573)
                  ·
                    refine ⟨660708223996330172957465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761888597323547127886573 660708223996330172957465)
                    ·
                      rfl

theorem cell22_1930087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1930087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930087 prefixEnd_1930087 := by exact prefixLift 1930087
  have htrace : WordTrace (prefixWord ++ tailWord_1930087) baseStart_1930087 baseEnd_1930087 := by
    simpa [prefixWord, tailWord_1930087, baseEnd_1930087] using wordTrace_append hprefix tailTrace_1930087
  have hstable : (prefixWord ++ tailWord_1930087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930087).length < 2 ^ (prefixWord ++ tailWord_1930087).sum := by decide
  have hdescent : baseEnd_1930087 < baseStart_1930087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930117 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 5]
def baseStart_1930117 : Nat := 118140960795 + 1930117 * 2 ^ 59
def prefixEnd_1930117 : Nat := 4983230072969 + 3 ^ 40 * 1930117 * 2
def baseEnd_1930117 : Nat := 220239497869806698235791

theorem tailTrace_1930117 : CollatzResearch.WordTrace tailWord_1930117 prefixEnd_1930117 220239497869806698235791 := by
  unfold tailWord_1930117
  simp only [CollatzResearch.WordTrace]
  refine ⟨70397150348523221584908605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46931433565682147723272403 70397150348523221584908605)
  ·
    refine ⟨26398931380696208094340727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70397150348523221584908605 26398931380696208094340727)
    ·
      refine ⟨39598397071044312141511091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26398931380696208094340727 39598397071044312141511091)
      ·
        refine ⟨59397595606566468212266637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39598397071044312141511091 59397595606566468212266637)
        ·
          refine ⟨22274098352462425579599989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59397595606566468212266637 22274098352462425579599989)
          ·
            refine ⟨2088196720543352398087499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22274098352462425579599989 2088196720543352398087499)
            ·
              refine ⟨3132295080815028597131249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088196720543352398087499 3132295080815028597131249)
              ·
                refine ⟨2349221310611271447848437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132295080815028597131249 2349221310611271447848437)
                ·
                  refine ⟨220239497869806698235791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2349221310611271447848437 220239497869806698235791)
                  ·
                    rfl

theorem cell22_1930117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_1930117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930117 prefixEnd_1930117 := by exact prefixLift 1930117
  have htrace : WordTrace (prefixWord ++ tailWord_1930117) baseStart_1930117 baseEnd_1930117 := by
    simpa [prefixWord, tailWord_1930117, baseEnd_1930117] using wordTrace_append hprefix tailTrace_1930117
  have hstable : (prefixWord ++ tailWord_1930117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930117).length < 2 ^ (prefixWord ++ tailWord_1930117).sum := by decide
  have hdescent : baseEnd_1930117 < baseStart_1930117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930190 : List Nat := [4, 1, 1, 1, 2, 3, 1, 9]
def baseStart_1930190 : Nat := 118140960795 + 1930190 * 2 ^ 59
def prefixEnd_1930190 : Nat := 4983230072969 + 3 ^ 40 * 1930190 * 2
def baseEnd_1930190 : Nat := 73415942555696915292461

theorem tailTrace_1930190 : CollatzResearch.WordTrace tailWord_1930190 prefixEnd_1930190 73415942555696915292461 := by
  unfold tailWord_1930190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799976609657344381539503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46933208584839170034877349 8799976609657344381539503)
  ·
    refine ⟨13199964914486016572309255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8799976609657344381539503 13199964914486016572309255)
    ·
      refine ⟨19799947371729024858463883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13199964914486016572309255 19799947371729024858463883)
      ·
        refine ⟨29699921057593537287695825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19799947371729024858463883 29699921057593537287695825)
        ·
          refine ⟨22274940793195152965771869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29699921057593537287695825 22274940793195152965771869)
          ·
            refine ⟨8353102797448182362164451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22274940793195152965771869 8353102797448182362164451)
            ·
              refine ⟨12529654196172273543246677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353102797448182362164451 12529654196172273543246677)
              ·
                refine ⟨73415942555696915292461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12529654196172273543246677 73415942555696915292461)
                ·
                  rfl

theorem cell22_1930190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_1930190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930190 prefixEnd_1930190 := by exact prefixLift 1930190
  have htrace : WordTrace (prefixWord ++ tailWord_1930190) baseStart_1930190 baseEnd_1930190 := by
    simpa [prefixWord, tailWord_1930190, baseEnd_1930190] using wordTrace_append hprefix tailTrace_1930190
  have hstable : (prefixWord ++ tailWord_1930190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930190).length < 2 ^ (prefixWord ++ tailWord_1930190).sum := by decide
  have hdescent : baseEnd_1930190 < baseStart_1930190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930252 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_1930252 : Nat := 118140960795 + 1930252 * 2 ^ 59
def prefixEnd_1930252 : Nat := 4983230072969 + 3 ^ 40 * 1930252 * 2
def baseEnd_1930252 : Nat := 220254902289441580860653

theorem tailTrace_1930252 : CollatzResearch.WordTrace tailWord_1930252 prefixEnd_1930252 220254902289441580860653 := by
  unfold tailWord_1930252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35201037101517069820536505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46934716135356093094048673 35201037101517069820536505)
  ·
    refine ⟨26400777826137802365402379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35201037101517069820536505 26400777826137802365402379)
    ·
      refine ⟨39601166739206703548103569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26400777826137802365402379 39601166739206703548103569)
      ·
        refine ⟨29700875054405027661077677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39601166739206703548103569 29700875054405027661077677)
        ·
          refine ⟨11137828145401885372904129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29700875054405027661077677 11137828145401885372904129)
          ·
            refine ⟨8353371109051414029678097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11137828145401885372904129 8353371109051414029678097)
            ·
              refine ⟨6265028331788560522258573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8353371109051414029678097 6265028331788560522258573)
              ·
                refine ⟨2349385624420710195846965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6265028331788560522258573 2349385624420710195846965)
                ·
                  refine ⟨220254902289441580860653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2349385624420710195846965 220254902289441580860653)
                  ·
                    rfl

theorem cell22_1930252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_1930252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930252 prefixEnd_1930252 := by exact prefixLift 1930252
  have htrace : WordTrace (prefixWord ++ tailWord_1930252) baseStart_1930252 baseEnd_1930252 := by
    simpa [prefixWord, tailWord_1930252, baseEnd_1930252] using wordTrace_append hprefix tailTrace_1930252
  have hstable : (prefixWord ++ tailWord_1930252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930252).length < 2 ^ (prefixWord ++ tailWord_1930252).sum := by decide
  have hdescent : baseEnd_1930252 < baseStart_1930252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930258 : List Nat := [3, 2, 5, 1, 1, 1, 3, 6]
def baseStart_1930258 : Nat := 118140960795 + 1930258 * 2 ^ 59
def prefixEnd_1930258 : Nat := 4983230072969 + 3 ^ 40 * 1930258 * 2
def baseEnd_1930258 : Nat := 73418528976771414103549

theorem tailTrace_1930258 : CollatzResearch.WordTrace tailWord_1930258 prefixEnd_1930258 73418528976771414103549 := by
  unfold tailWord_1930258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17600573260253100666447857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46934862027341601777194285 17600573260253100666447857)
  ·
    refine ⟨13200429945189825499835893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17600573260253100666447857 13200429945189825499835893)
    ·
      refine ⟨1237540307361546140609615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13200429945189825499835893 1237540307361546140609615)
      ·
        refine ⟨1856310461042319210914423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237540307361546140609615 1856310461042319210914423)
        ·
          refine ⟨2784465691563478816371635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856310461042319210914423 2784465691563478816371635)
          ·
            refine ⟨4176698537345218224557453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784465691563478816371635 4176698537345218224557453)
            ·
              refine ⟨1566261951504456834209045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4176698537345218224557453 1566261951504456834209045)
              ·
                refine ⟨73418528976771414103549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1566261951504456834209045 73418528976771414103549)
                ·
                  rfl

theorem cell22_1930258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_1930258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930258 prefixEnd_1930258 := by exact prefixLift 1930258
  have htrace : WordTrace (prefixWord ++ tailWord_1930258) baseStart_1930258 baseEnd_1930258 := by
    simpa [prefixWord, tailWord_1930258, baseEnd_1930258] using wordTrace_append hprefix tailTrace_1930258
  have hstable : (prefixWord ++ tailWord_1930258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930258).length < 2 ^ (prefixWord ++ tailWord_1930258).sum := by decide
  have hdescent : baseEnd_1930258 < baseStart_1930258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930297 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 6]
def baseStart_1930297 : Nat := 118140960795 + 1930297 * 2 ^ 59
def prefixEnd_1930297 : Nat := 4983230072969 + 3 ^ 40 * 1930297 * 2
def baseEnd_1930297 : Nat := 220260037095986541735607

theorem tailTrace_1930297 : CollatzResearch.WordTrace tailWord_1930297 prefixEnd_1930297 220260037095986541735607 := by
  unfold tailWord_1930297
  simp only [CollatzResearch.WordTrace]
  refine ⟨70403715487871112326461145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46935810325247408217640763 70403715487871112326461145)
  ·
    refine ⟨52802786615903334244845859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70403715487871112326461145 52802786615903334244845859)
    ·
      refine ⟨79204179923855001367268789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52802786615903334244845859 79204179923855001367268789)
      ·
        refine ⟨7425391867861406378181449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79204179923855001367268789 7425391867861406378181449)
        ·
          refine ⟨5569043900896054783636087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425391867861406378181449 5569043900896054783636087)
          ·
            refine ⟨8353565851344082175454131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569043900896054783636087 8353565851344082175454131)
            ·
              refine ⟨12530348777016123263181197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353565851344082175454131 12530348777016123263181197)
              ·
                refine ⟨4698880791381046223692949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12530348777016123263181197 4698880791381046223692949)
                ·
                  refine ⟨220260037095986541735607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4698880791381046223692949 220260037095986541735607)
                  ·
                    rfl

theorem cell22_1930297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_1930297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930297 prefixEnd_1930297 := by exact prefixLift 1930297
  have htrace : WordTrace (prefixWord ++ tailWord_1930297) baseStart_1930297 baseEnd_1930297 := by
    simpa [prefixWord, tailWord_1930297, baseEnd_1930297] using wordTrace_append hprefix tailTrace_1930297
  have hstable : (prefixWord ++ tailWord_1930297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930297).length < 2 ^ (prefixWord ++ tailWord_1930297).sum := by decide
  have hdescent : baseEnd_1930297 < baseStart_1930297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930327 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 2, 4]
def baseStart_1930327 : Nat := 118140960795 + 1930327 * 2 ^ 59
def prefixEnd_1930327 : Nat := 4983230072969 + 3 ^ 40 * 1930327 * 2
def baseEnd_1930327 : Nat := 660790380901049546956729

theorem tailTrace_1930327 : CollatzResearch.WordTrace tailWord_1930327 prefixEnd_1930327 660790380901049546956729 := by
  unfold tailWord_1930327
  simp only [CollatzResearch.WordTrace]
  refine ⟨70404809677762427450053235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46936539785174951633368823 70404809677762427450053235)
  ·
    refine ⟨105607214516643641175079853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70404809677762427450053235 105607214516643641175079853)
    ·
      refine ⟨39602705443741365440654945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105607214516643641175079853 39602705443741365440654945)
      ·
        refine ⟨29702029082806024080491209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39602705443741365440654945 29702029082806024080491209)
        ·
          refine ⟨22276521812104518060368407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29702029082806024080491209 22276521812104518060368407)
          ·
            refine ⟨33414782718156777090552611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22276521812104518060368407 33414782718156777090552611)
            ·
              refine ⟨50122174077235165635828917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33414782718156777090552611 50122174077235165635828917)
              ·
                refine ⟨4698953819740796778358961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50122174077235165635828917 4698953819740796778358961)
                ·
                  refine ⟨3524215364805597583769221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698953819740796778358961 3524215364805597583769221)
                  ·
                    refine ⟨660790380901049546956729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3524215364805597583769221 660790380901049546956729)
                    ·
                      rfl

theorem cell22_1930327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1930327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930327 prefixEnd_1930327 := by exact prefixLift 1930327
  have htrace : WordTrace (prefixWord ++ tailWord_1930327) baseStart_1930327 baseEnd_1930327 := by
    simpa [prefixWord, tailWord_1930327, baseEnd_1930327] using wordTrace_append hprefix tailTrace_1930327
  have hstable : (prefixWord ++ tailWord_1930327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930327).length < 2 ^ (prefixWord ++ tailWord_1930327).sum := by decide
  have hdescent : baseEnd_1930327 < baseStart_1930327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930404 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_1930404 : Nat := 118140960795 + 1930404 * 2 ^ 59
def prefixEnd_1930404 : Nat := 4983230072969 + 3 ^ 40 * 1930404 * 2
def baseEnd_1930404 : Nat := 220272246524882337593831

theorem tailTrace_1930404 : CollatzResearch.WordTrace tailWord_1930404 prefixEnd_1930404 220272246524882337593831 := by
  unfold tailWord_1930404
  simp only [CollatzResearch.WordTrace]
  refine ⟨35203809049241734800303133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46938412065655646400404177 35203809049241734800303133)
  ·
    refine ⟨13201428393465650550113675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35203809049241734800303133 13201428393465650550113675)
    ·
      refine ⟨19802142590198475825170513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201428393465650550113675 19802142590198475825170513)
      ·
        refine ⟨14851606942648856868877885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19802142590198475825170513 14851606942648856868877885)
        ·
          refine ⟨5569352603493321325829207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14851606942648856868877885 5569352603493321325829207)
          ·
            refine ⟨8354028905239981988743811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569352603493321325829207 8354028905239981988743811)
            ·
              refine ⟨12531043357859972983115717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354028905239981988743811 12531043357859972983115717)
              ·
                refine ⟨2349570629598744934334197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12531043357859972983115717 2349570629598744934334197)
                ·
                  refine ⟨220272246524882337593831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2349570629598744934334197 220272246524882337593831)
                  ·
                    rfl

theorem cell22_1930404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_1930404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930404 prefixEnd_1930404 := by exact prefixLift 1930404
  have htrace : WordTrace (prefixWord ++ tailWord_1930404) baseStart_1930404 baseEnd_1930404 := by
    simpa [prefixWord, tailWord_1930404, baseEnd_1930404] using wordTrace_append hprefix tailTrace_1930404
  have hstable : (prefixWord ++ tailWord_1930404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930404).length < 2 ^ (prefixWord ++ tailWord_1930404).sum := by decide
  have hdescent : baseEnd_1930404 < baseStart_1930404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930447 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_1930447 : Nat := 118140960795 + 1930447 * 2 ^ 59
def prefixEnd_1930447 : Nat := 4983230072969 + 3 ^ 40 * 1930447 * 2
def baseEnd_1930447 : Nat := 660831459353409233956361

theorem tailTrace_1930447 : CollatzResearch.WordTrace tailWord_1930447 prefixEnd_1930447 660831459353409233956361 := by
  unfold tailWord_1930447
  simp only [CollatzResearch.WordTrace]
  refine ⟨70409186437327687944421595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46939457624885125296281063 70409186437327687944421595)
  ·
    refine ⟨105613779655991531916632393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70409186437327687944421595 105613779655991531916632393)
    ·
      refine ⟨79210334741993648937474295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105613779655991531916632393 79210334741993648937474295)
      ·
        refine ⟨118815502112990473406211443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79210334741993648937474295 118815502112990473406211443)
        ·
          refine ⟨178223253169485710109317165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118815502112990473406211443 178223253169485710109317165)
          ·
            refine ⟨66833719938557141290993937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178223253169485710109317165 66833719938557141290993937)
            ·
              refine ⟨50125289953917855968245453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66833719938557141290993937 50125289953917855968245453)
              ·
                refine ⟨18796983732719195988092045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50125289953917855968245453 18796983732719195988092045)
                ·
                  refine ⟨7048868899769698495534517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18796983732719195988092045 7048868899769698495534517)
                  ·
                    refine ⟨660831459353409233956361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7048868899769698495534517 660831459353409233956361)
                    ·
                      rfl

theorem cell22_1930447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_1930447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930447 prefixEnd_1930447 := by exact prefixLift 1930447
  have htrace : WordTrace (prefixWord ++ tailWord_1930447) baseStart_1930447 baseEnd_1930447 := by
    simpa [prefixWord, tailWord_1930447, baseEnd_1930447] using wordTrace_append hprefix tailTrace_1930447
  have hstable : (prefixWord ++ tailWord_1930447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930447).length < 2 ^ (prefixWord ++ tailWord_1930447).sum := by decide
  have hdescent : baseEnd_1930447 < baseStart_1930447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930584 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_1930584 : Nat := 118140960795 + 1930584 * 2 ^ 59
def prefixEnd_1930584 : Nat := 4983230072969 + 3 ^ 40 * 1930584 * 2
def baseEnd_1930584 : Nat := 220292785751062181093647

theorem tailTrace_1930584 : CollatzResearch.WordTrace tailWord_1930584 prefixEnd_1930584 220292785751062181093647 := by
  unfold tailWord_1930584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207091618915680171079403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46942788825220906894772537 35207091618915680171079403)
  ·
    refine ⟨52810637428373520256619105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35207091618915680171079403 52810637428373520256619105)
    ·
      refine ⟨39607978071280140192464329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52810637428373520256619105 39607978071280140192464329)
      ·
        refine ⟨29705983553460105144348247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39607978071280140192464329 29705983553460105144348247)
        ·
          refine ⟨44558975330190157716522371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29705983553460105144348247 44558975330190157716522371)
          ·
            refine ⟨66838462995285236574783557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44558975330190157716522371 66838462995285236574783557)
            ·
              refine ⟨12532211811615981857771917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66838462995285236574783557 12532211811615981857771917)
              ·
                refine ⟨4699579429355993196664469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12532211811615981857771917 4699579429355993196664469)
                ·
                  refine ⟨220292785751062181093647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4699579429355993196664469 220292785751062181093647)
                  ·
                    rfl

theorem cell22_1930584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_1930584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930584 prefixEnd_1930584 := by exact prefixLift 1930584
  have htrace : WordTrace (prefixWord ++ tailWord_1930584) baseStart_1930584 baseEnd_1930584 := by
    simpa [prefixWord, tailWord_1930584, baseEnd_1930584] using wordTrace_append hprefix tailTrace_1930584
  have hstable : (prefixWord ++ tailWord_1930584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930584).length < 2 ^ (prefixWord ++ tailWord_1930584).sum := by decide
  have hdescent : baseEnd_1930584 < baseStart_1930584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930633 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_1930633 : Nat := 118140960795 + 1930633 * 2 ^ 59
def prefixEnd_1930633 : Nat := 4983230072969 + 3 ^ 40 * 1930633 * 2
def baseEnd_1930633 : Nat := 660895130954566748805791

theorem tailTrace_1930633 : CollatzResearch.WordTrace tailWord_1930633 prefixEnd_1930633 660895130954566748805791 := by
  unfold tailWord_1930633
  simp only [CollatzResearch.WordTrace]
  refine ⟨70415970414653841710692553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46943980276435894473795035 70415970414653841710692553)
  ·
    refine ⟨52811977810990381283019415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70415970414653841710692553 52811977810990381283019415)
    ·
      refine ⟨79217966716485571924529123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52811977810990381283019415 79217966716485571924529123)
      ·
        refine ⟨118826950074728357886793685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79217966716485571924529123 118826950074728357886793685)
        ·
          refine ⟨2785006642376445887971727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118826950074728357886793685 2785006642376445887971727)
          ·
            refine ⟨4177509963564668831957591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785006642376445887971727 4177509963564668831957591)
            ·
              refine ⟨6266264945347003247936387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177509963564668831957591 6266264945347003247936387)
              ·
                refine ⟨9399397418020504871904581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266264945347003247936387 9399397418020504871904581)
                ·
                  refine ⟨1762387015878844663482109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9399397418020504871904581 1762387015878844663482109)
                  ·
                    refine ⟨660895130954566748805791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1762387015878844663482109 660895130954566748805791)
                    ·
                      rfl

theorem cell22_1930633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_1930633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930633 prefixEnd_1930633 := by exact prefixLift 1930633
  have htrace : WordTrace (prefixWord ++ tailWord_1930633) baseStart_1930633 baseEnd_1930633 := by
    simpa [prefixWord, tailWord_1930633, baseEnd_1930633] using wordTrace_append hprefix tailTrace_1930633
  have hstable : (prefixWord ++ tailWord_1930633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930633).length < 2 ^ (prefixWord ++ tailWord_1930633).sum := by decide
  have hdescent : baseEnd_1930633 < baseStart_1930633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930650 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_1930650 : Nat := 118140960795 + 1930650 * 2 ^ 59
def prefixEnd_1930650 : Nat := 4983230072969 + 3 ^ 40 * 1930650 * 2
def baseEnd_1930650 : Nat := 660900950401984371130739

theorem tailTrace_1930650 : CollatzResearch.WordTrace tailWord_1930650 prefixEnd_1930650 660900950401984371130739 := by
  unfold tailWord_1930650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17604147613898063403515351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46944393637061502409374269 17604147613898063403515351)
  ·
    refine ⟨26406221420847095105273027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17604147613898063403515351 26406221420847095105273027)
    ·
      refine ⟨39609332131270642657909541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26406221420847095105273027 39609332131270642657909541)
      ·
        refine ⟨7426749774613245498358039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39609332131270642657909541 7426749774613245498358039)
        ·
          refine ⟨11140124661919868247537059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426749774613245498358039 11140124661919868247537059)
          ·
            refine ⟨16710186992879802371305589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11140124661919868247537059 16710186992879802371305589)
            ·
              refine ⟨1566580030582481472309899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16710186992879802371305589 1566580030582481472309899)
              ·
                refine ⟨2349870045873722208464849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566580030582481472309899 2349870045873722208464849)
                ·
                  refine ⟨1762402534405291656348637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349870045873722208464849 1762402534405291656348637)
                  ·
                    refine ⟨660900950401984371130739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1762402534405291656348637 660900950401984371130739)
                    ·
                      rfl

theorem cell22_1930650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_1930650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930650 prefixEnd_1930650 := by exact prefixLift 1930650
  have htrace : WordTrace (prefixWord ++ tailWord_1930650) baseStart_1930650 baseEnd_1930650 := by
    simpa [prefixWord, tailWord_1930650, baseEnd_1930650] using wordTrace_append hprefix tailTrace_1930650
  have hstable : (prefixWord ++ tailWord_1930650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930650).length < 2 ^ (prefixWord ++ tailWord_1930650).sum := by decide
  have hdescent : baseEnd_1930650 < baseStart_1930650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930661 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_1930661 : Nat := 118140960795 + 1930661 * 2 ^ 59
def prefixEnd_1930661 : Nat := 4983230072969 + 3 ^ 40 * 1930661 * 2
def baseEnd_1930661 : Nat := 660904715926784009105705

theorem tailTrace_1930661 : CollatzResearch.WordTrace tailWord_1930661 prefixEnd_1930661 660904715926784009105705 := by
  unfold tailWord_1930661
  simp only [CollatzResearch.WordTrace]
  refine ⟨70416991658552402492711837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46944661105701601661807891 70416991658552402492711837)
  ·
    refine ⟨26406371871957150934766939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70416991658552402492711837 26406371871957150934766939)
    ·
      refine ⟨39609557807935726402150409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26406371871957150934766939 39609557807935726402150409)
      ·
        refine ⟨29707168355951794801612807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39609557807935726402150409 29707168355951794801612807)
        ·
          refine ⟨44560752533927692202419211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29707168355951794801612807 44560752533927692202419211)
          ·
            refine ⟨66841128800891538303628817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44560752533927692202419211 66841128800891538303628817)
            ·
              refine ⟨50130846600668653727721613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66841128800891538303628817 50130846600668653727721613)
              ·
                refine ⟨18799067475250745147895605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50130846600668653727721613 18799067475250745147895605)
                ·
                  refine ⟨1762412575804757357615213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18799067475250745147895605 1762412575804757357615213)
                  ·
                    refine ⟨660904715926784009105705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1762412575804757357615213 660904715926784009105705)
                    ·
                      rfl

theorem cell22_1930661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_1930661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930661 prefixEnd_1930661 := by exact prefixLift 1930661
  have htrace : WordTrace (prefixWord ++ tailWord_1930661) baseStart_1930661 baseEnd_1930661 := by
    simpa [prefixWord, tailWord_1930661, baseEnd_1930661] using wordTrace_append hprefix tailTrace_1930661
  have hstable : (prefixWord ++ tailWord_1930661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930661).length < 2 ^ (prefixWord ++ tailWord_1930661).sum := by decide
  have hdescent : baseEnd_1930661 < baseStart_1930661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930783 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 2, 4]
def baseStart_1930783 : Nat := 118140960795 + 1930783 * 2 ^ 59
def prefixEnd_1930783 : Nat := 4983230072969 + 3 ^ 40 * 1930783 * 2
def baseEnd_1930783 : Nat := 660946479020016357555331

theorem tailTrace_1930783 : CollatzResearch.WordTrace tailWord_1930783 prefixEnd_1930783 660946479020016357555331 := by
  unfold tailWord_1930783
  simp only [CollatzResearch.WordTrace]
  refine ⟨70421441364110417328653003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46947627576073611552435335 70421441364110417328653003)
  ·
    refine ⟨105632162046165625992979505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70421441364110417328653003 105632162046165625992979505)
    ·
      refine ⟨79224121534624219494734629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105632162046165625992979505 79224121534624219494734629)
      ·
        refine ⟨14854522787742041155262743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79224121534624219494734629 14854522787742041155262743)
        ·
          refine ⟨22281784181613061732894115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14854522787742041155262743 22281784181613061732894115)
          ·
            refine ⟨33422676272419592599341173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22281784181613061732894115 33422676272419592599341173)
            ·
              refine ⟨3133375900539336806188235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33422676272419592599341173 3133375900539336806188235)
              ·
                refine ⟨4700063850809005209282353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133375900539336806188235 4700063850809005209282353)
                ·
                  refine ⟨3525047888106753906961765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4700063850809005209282353 3525047888106753906961765)
                  ·
                    refine ⟨660946479020016357555331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525047888106753906961765 660946479020016357555331)
                    ·
                      rfl

theorem cell22_1930783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_1930783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930783 prefixEnd_1930783 := by exact prefixLift 1930783
  have htrace : WordTrace (prefixWord ++ tailWord_1930783) baseStart_1930783 baseEnd_1930783 := by
    simpa [prefixWord, tailWord_1930783, baseEnd_1930783] using wordTrace_append hprefix tailTrace_1930783
  have hstable : (prefixWord ++ tailWord_1930783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930783).length < 2 ^ (prefixWord ++ tailWord_1930783).sum := by decide
  have hdescent : baseEnd_1930783 < baseStart_1930783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930798 : List Nat := [4, 1, 3, 1, 2, 2, 9]
def baseStart_1930798 : Nat := 118140960795 + 1930798 * 2 ^ 59
def prefixEnd_1930798 : Nat := 4983230072969 + 3 ^ 40 * 1930798 * 2
def baseEnd_1930798 : Nat := 24479689400983752534455

theorem tailTrace_1930798 : CollatzResearch.WordTrace tailWord_1930798 prefixEnd_1930798 24479689400983752534455 := by
  unfold tailWord_1930798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802748557382009361306131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46947992306037383260299365 8802748557382009361306131)
  ·
    refine ⟨13204122836073014041959197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8802748557382009361306131 13204122836073014041959197)
    ·
      refine ⟨4951546063527380265734699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13204122836073014041959197 4951546063527380265734699)
      ·
        refine ⟨7427319095291070398602049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951546063527380265734699 7427319095291070398602049)
        ·
          refine ⟨5570489321468302798951537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7427319095291070398602049 5570489321468302798951537)
          ·
            refine ⟨4177866991101227099213653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570489321468302798951537 4177866991101227099213653)
            ·
              refine ⟨24479689400983752534455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4177866991101227099213653 24479689400983752534455)
              ·
                rfl

theorem cell22_1930798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 9].length) (baseStart_1930798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930798 prefixEnd_1930798 := by exact prefixLift 1930798
  have htrace : WordTrace (prefixWord ++ tailWord_1930798) baseStart_1930798 baseEnd_1930798 := by
    simpa [prefixWord, tailWord_1930798, baseEnd_1930798] using wordTrace_append hprefix tailTrace_1930798
  have hstable : (prefixWord ++ tailWord_1930798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930798).length < 2 ^ (prefixWord ++ tailWord_1930798).sum := by decide
  have hdescent : baseEnd_1930798 < baseStart_1930798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930838 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1930838 : Nat := 118140960795 + 1930838 * 2 ^ 59
def prefixEnd_1930838 : Nat := 4983230072969 + 3 ^ 40 * 1930838 * 2
def baseEnd_1930838 : Nat := 220321768881338182476721

theorem tailTrace_1930838 : CollatzResearch.WordTrace tailWord_1930838 prefixEnd_1930838 220321768881338182476721 := by
  unfold tailWord_1930838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401465461181947607619073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46948964919274107814603445 4401465461181947607619073)
  ·
    refine ⟨3301099095886460705714305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4401465461181947607619073 3301099095886460705714305)
    ·
      refine ⟨2475824321914845529285729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3301099095886460705714305 2475824321914845529285729)
      ·
        refine ⟨1856868241436134146964297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2475824321914845529285729 1856868241436134146964297)
        ·
          refine ⟨1392651181077100610223223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856868241436134146964297 1392651181077100610223223)
          ·
            refine ⟨2088976771615650915334835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392651181077100610223223 2088976771615650915334835)
            ·
              refine ⟨3133465157423476373002253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088976771615650915334835 3133465157423476373002253)
              ·
                refine ⟨1175049434033803639875845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133465157423476373002253 1175049434033803639875845)
                ·
                  refine ⟨220321768881338182476721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1175049434033803639875845 220321768881338182476721)
                  ·
                    rfl

theorem cell22_1930838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1930838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930838 prefixEnd_1930838 := by exact prefixLift 1930838
  have htrace : WordTrace (prefixWord ++ tailWord_1930838) baseStart_1930838 baseEnd_1930838 := by
    simpa [prefixWord, tailWord_1930838, baseEnd_1930838] using wordTrace_append hprefix tailTrace_1930838
  have hstable : (prefixWord ++ tailWord_1930838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930838).length < 2 ^ (prefixWord ++ tailWord_1930838).sum := by decide
  have hdescent : baseEnd_1930838 < baseStart_1930838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930841 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_1930841 : Nat := 118140960795 + 1930841 * 2 ^ 59
def prefixEnd_1930841 : Nat := 4983230072969 + 3 ^ 40 * 1930841 * 2
def baseEnd_1930841 : Nat := 660966333605323539605153

theorem tailTrace_1930841 : CollatzResearch.WordTrace tailWord_1930841 prefixEnd_1930841 660966333605323539605153 := by
  unfold tailWord_1930841
  simp only [CollatzResearch.WordTrace]
  refine ⟨70423556797900293234264377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46949037865266862156176251 70423556797900293234264377)
  ·
    refine ⟨52817667598425219925698283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70423556797900293234264377 52817667598425219925698283)
    ·
      refine ⟨79226501397637829888547425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52817667598425219925698283 79226501397637829888547425)
      ·
        refine ⟨59419876048228372416410569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79226501397637829888547425 59419876048228372416410569)
        ·
          refine ⟨44564907036171279312307927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59419876048228372416410569 44564907036171279312307927)
          ·
            refine ⟨66847360554256918968461891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44564907036171279312307927 66847360554256918968461891)
            ·
              refine ⟨100271040831385378452692837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66847360554256918968461891 100271040831385378452692837)
              ·
                refine ⟨18800820155884758459879907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100271040831385378452692837 18800820155884758459879907)
                ·
                  refine ⟨28201230233827137689819861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18800820155884758459879907 28201230233827137689819861)
                  ·
                    refine ⟨660966333605323539605153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28201230233827137689819861 660966333605323539605153)
                    ·
                      rfl

theorem cell22_1930841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_1930841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930841 prefixEnd_1930841 := by exact prefixLift 1930841
  have htrace : WordTrace (prefixWord ++ tailWord_1930841) baseStart_1930841 baseEnd_1930841 := by
    simpa [prefixWord, tailWord_1930841, baseEnd_1930841] using wordTrace_append hprefix tailTrace_1930841
  have hstable : (prefixWord ++ tailWord_1930841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930841).length < 2 ^ (prefixWord ++ tailWord_1930841).sum := by decide
  have hdescent : baseEnd_1930841 < baseStart_1930841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930864 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 1, 3]
def baseStart_1930864 : Nat := 118140960795 + 1930864 * 2 ^ 59
def prefixEnd_1930864 : Nat := 4983230072969 + 3 ^ 40 * 1930864 * 2
def baseEnd_1930864 : Nat := 660974206975359146280083

theorem tailTrace_1930864 : CollatzResearch.WordTrace tailWord_1930864 prefixEnd_1930864 660974206975359146280083 := by
  unfold tailWord_1930864
  simp only [CollatzResearch.WordTrace]
  refine ⟨35212197838408484081175823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46949597117877978774901097 35212197838408484081175823)
  ·
    refine ⟨52818296757612726121763735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35212197838408484081175823 52818296757612726121763735)
    ·
      refine ⟨79227445136419089182645603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52818296757612726121763735 79227445136419089182645603)
      ·
        refine ⟨118841167704628633773968405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79227445136419089182645603 118841167704628633773968405)
        ·
          refine ⟨5570679736154467208154769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118841167704628633773968405 5570679736154467208154769)
          ·
            refine ⟨4178009802115850406116077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570679736154467208154769 4178009802115850406116077)
            ·
              refine ⟨1566753675793443902293529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4178009802115850406116077 1566753675793443902293529)
              ·
                refine ⟨1175065256845082926720147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566753675793443902293529 1175065256845082926720147)
                ·
                  refine ⟨1762597885267624390080221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175065256845082926720147 1762597885267624390080221)
                  ·
                    refine ⟨660974206975359146280083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1762597885267624390080221 660974206975359146280083)
                    ·
                      rfl

theorem cell22_1930864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_1930864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930864 prefixEnd_1930864 := by exact prefixLift 1930864
  have htrace : WordTrace (prefixWord ++ tailWord_1930864) baseStart_1930864 baseEnd_1930864 := by
    simpa [prefixWord, tailWord_1930864, baseEnd_1930864] using wordTrace_append hprefix tailTrace_1930864
  have hstable : (prefixWord ++ tailWord_1930864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930864).length < 2 ^ (prefixWord ++ tailWord_1930864).sum := by decide
  have hdescent : baseEnd_1930864 < baseStart_1930864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930873 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_1930873 : Nat := 118140960795 + 1930873 * 2 ^ 59
def prefixEnd_1930873 : Nat := 4983230072969 + 3 ^ 40 * 1930873 * 2
def baseEnd_1930873 : Nat := 660977287859286122805055

theorem tailTrace_1930873 : CollatzResearch.WordTrace tailWord_1930873 prefixEnd_1930873 660977287859286122805055 := by
  unfold tailWord_1930873
  simp only [CollatzResearch.WordTrace]
  refine ⟨70424723933784362699429273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46949815955856241799619515 70424723933784362699429273)
  ·
    refine ⟨52818542950338272024571955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70424723933784362699429273 52818542950338272024571955)
    ·
      refine ⟨79227814425507408036857933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52818542950338272024571955 79227814425507408036857933)
      ·
        refine ⟨29710430409565278013821725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79227814425507408036857933 29710430409565278013821725)
        ·
          refine ⟨11141411403586979255183147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29710430409565278013821725 11141411403586979255183147)
          ·
            refine ⟨16712117105380468882774721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11141411403586979255183147 16712117105380468882774721)
            ·
              refine ⟨12534087829035351662081041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16712117105380468882774721 12534087829035351662081041)
              ·
                refine ⟨9400565871776513746560781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12534087829035351662081041 9400565871776513746560781)
                ·
                  refine ⟨3525212201916192654960293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9400565871776513746560781 3525212201916192654960293)
                  ·
                    refine ⟨660977287859286122805055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525212201916192654960293 660977287859286122805055)
                    ·
                      rfl

theorem cell22_1930873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_1930873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930873 prefixEnd_1930873 := by exact prefixLift 1930873
  have htrace : WordTrace (prefixWord ++ tailWord_1930873) baseStart_1930873 baseEnd_1930873 := by
    simpa [prefixWord, tailWord_1930873, baseEnd_1930873] using wordTrace_append hprefix tailTrace_1930873
  have hstable : (prefixWord ++ tailWord_1930873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930873).length < 2 ^ (prefixWord ++ tailWord_1930873).sum := by decide
  have hdescent : baseEnd_1930873 < baseStart_1930873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930877 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 5]
def baseStart_1930877 : Nat := 118140960795 + 1930877 * 2 ^ 59
def prefixEnd_1930877 : Nat := 4983230072969 + 3 ^ 40 * 1930877 * 2
def baseEnd_1930877 : Nat := 220326219047010481901681

theorem tailTrace_1930877 : CollatzResearch.WordTrace tailWord_1930877 prefixEnd_1930877 220326219047010481901681 := by
  unfold tailWord_1930877
  simp only [CollatzResearch.WordTrace]
  refine ⟨70424869825769871382574885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46949913217179914255049923 70424869825769871382574885)
  ·
    refine ⟨13204663092331850884232791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70424869825769871382574885 13204663092331850884232791)
    ·
      refine ⟨19806994638497776326349187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13204663092331850884232791 19806994638497776326349187)
      ·
        refine ⟨29710491957746664489523781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19806994638497776326349187 29710491957746664489523781)
        ·
          refine ⟨5570717242077499591785709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29710491957746664489523781 5570717242077499591785709)
          ·
            refine ⟨2089018965779062346919641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5570717242077499591785709 2089018965779062346919641)
            ·
              refine ⟨1566764224334296760189731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089018965779062346919641 1566764224334296760189731)
              ·
                refine ⟨2350146336501445140284597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566764224334296760189731 2350146336501445140284597)
                ·
                  refine ⟨220326219047010481901681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2350146336501445140284597 220326219047010481901681)
                  ·
                    rfl

theorem cell22_1930877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_1930877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930877 prefixEnd_1930877 := by exact prefixLift 1930877
  have htrace : WordTrace (prefixWord ++ tailWord_1930877) baseStart_1930877 baseEnd_1930877 := by
    simpa [prefixWord, tailWord_1930877, baseEnd_1930877] using wordTrace_append hprefix tailTrace_1930877
  have hstable : (prefixWord ++ tailWord_1930877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930877).length < 2 ^ (prefixWord ++ tailWord_1930877).sum := by decide
  have hdescent : baseEnd_1930877 < baseStart_1930877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930890 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1930890 : Nat := 118140960795 + 1930890 * 2 ^ 59
def prefixEnd_1930890 : Nat := 4983230072969 + 3 ^ 40 * 1930890 * 2
def baseEnd_1930890 : Nat := 660983107306703745130003

theorem tailTrace_1930890 : CollatzResearch.WordTrace tailWord_1930890 prefixEnd_1930890 660983107306703745130003 := by
  unfold tailWord_1930890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606335993680693650699531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46950229316481849735198749 17606335993680693650699531)
  ·
    refine ⟨26409503990521040476049297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17606335993680693650699531 26409503990521040476049297)
    ·
      refine ⟨19807127992890780357036973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26409503990521040476049297 19807127992890780357036973)
      ·
        refine ⟨7427672997334042633888865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19807127992890780357036973 7427672997334042633888865)
        ·
          refine ⟨5570754748000531975416649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7427672997334042633888865 5570754748000531975416649)
          ·
            refine ⟨4178066061000398981562487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570754748000531975416649 4178066061000398981562487)
            ·
              refine ⟨6267099091500598472343731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178066061000398981562487 6267099091500598472343731)
              ·
                refine ⟨9400648637250897708515597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267099091500598472343731 9400648637250897708515597)
                ·
                  refine ⟨3525243238969086640693349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9400648637250897708515597 3525243238969086640693349)
                  ·
                    refine ⟨660983107306703745130003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525243238969086640693349 660983107306703745130003)
                    ·
                      rfl

theorem cell22_1930890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1930890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930890 prefixEnd_1930890 := by exact prefixLift 1930890
  have htrace : WordTrace (prefixWord ++ tailWord_1930890) baseStart_1930890 baseEnd_1930890 := by
    simpa [prefixWord, tailWord_1930890, baseEnd_1930890] using wordTrace_append hprefix tailTrace_1930890
  have hstable : (prefixWord ++ tailWord_1930890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930890).length < 2 ^ (prefixWord ++ tailWord_1930890).sum := by decide
  have hdescent : baseEnd_1930890 < baseStart_1930890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930903 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_1930903 : Nat := 118140960795 + 1930903 * 2 ^ 59
def prefixEnd_1930903 : Nat := 4983230072969 + 3 ^ 40 * 1930903 * 2
def baseEnd_1930903 : Nat := 660987557472376044554963

theorem tailTrace_1930903 : CollatzResearch.WordTrace tailWord_1930903 prefixEnd_1930903 660987557472376044554963 := by
  unfold tailWord_1930903
  simp only [CollatzResearch.WordTrace]
  refine ⟨70425818123675677823021363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46950545415783785215347575 70425818123675677823021363)
  ·
    refine ⟨105638727185513516734532045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70425818123675677823021363 105638727185513516734532045)
    ·
      refine ⟨39614522694567568775449517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105638727185513516734532045 39614522694567568775449517)
      ·
        refine ⟨14855446010462838290793569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39614522694567568775449517 14855446010462838290793569)
        ·
          refine ⟨11141584507847128718095177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14855446010462838290793569 11141584507847128718095177)
          ·
            refine ⟨8356188380885346538571383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11141584507847128718095177 8356188380885346538571383)
            ·
              refine ⟨12534282571328019807857075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356188380885346538571383 12534282571328019807857075)
              ·
                refine ⟨18801423856992029711785613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534282571328019807857075 18801423856992029711785613)
                ·
                  refine ⟨7050533946372011141919605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18801423856992029711785613 7050533946372011141919605)
                  ·
                    refine ⟨660987557472376044554963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7050533946372011141919605 660987557472376044554963)
                    ·
                      rfl

theorem cell22_1930903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_1930903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1930903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1930903 prefixEnd_1930903 := by exact prefixLift 1930903
  have htrace : WordTrace (prefixWord ++ tailWord_1930903) baseStart_1930903 baseEnd_1930903 := by
    simpa [prefixWord, tailWord_1930903, baseEnd_1930903] using wordTrace_append hprefix tailTrace_1930903
  have hstable : (prefixWord ++ tailWord_1930903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930903).length < 2 ^ (prefixWord ++ tailWord_1930903).sum := by decide
  have hdescent : baseEnd_1930903 < baseStart_1930903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931059 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 1, 4]
def baseStart_1931059 : Nat := 118140960795 + 1931059 * 2 ^ 59
def prefixEnd_1931059 : Nat := 4983230072969 + 3 ^ 40 * 1931059 * 2
def baseEnd_1931059 : Nat := 661040959460443637654485

theorem tailTrace_1931059 : CollatzResearch.WordTrace tailWord_1931059 prefixEnd_1931059 661040959460443637654485 := by
  unfold tailWord_1931059
  simp only [CollatzResearch.WordTrace]
  refine ⟨70431507911110516465700231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46954338607407010977133487 70431507911110516465700231)
  ·
    refine ⟨105647261866665774698550347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70431507911110516465700231 105647261866665774698550347)
    ·
      refine ⟨158470892799998662047825521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105647261866665774698550347 158470892799998662047825521)
      ·
        refine ⟨118853169599998996535869141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158470892799998662047825521 118853169599998996535869141)
        ·
          refine ⟨2785621162499976481309433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118853169599998996535869141 2785621162499976481309433)
          ·
            refine ⟨2089215871874982360982075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2785621162499976481309433 2089215871874982360982075)
            ·
              refine ⟨3133823807812473541473113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089215871874982360982075 3133823807812473541473113)
              ·
                refine ⟨2350367855859355156104835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133823807812473541473113 2350367855859355156104835)
                ·
                  refine ⟨3525551783789032734157253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350367855859355156104835 3525551783789032734157253)
                  ·
                    refine ⟨661040959460443637654485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525551783789032734157253 661040959460443637654485)
                    ·
                      rfl

theorem cell22_1931059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 4].length) (baseStart_1931059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931059 prefixEnd_1931059 := by exact prefixLift 1931059
  have htrace : WordTrace (prefixWord ++ tailWord_1931059) baseStart_1931059 baseEnd_1931059 := by
    simpa [prefixWord, tailWord_1931059, baseEnd_1931059] using wordTrace_append hprefix tailTrace_1931059
  have hstable : (prefixWord ++ tailWord_1931059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931059).length < 2 ^ (prefixWord ++ tailWord_1931059).sum := by decide
  have hdescent : baseEnd_1931059 < baseStart_1931059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931089 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_1931089 : Nat := 118140960795 + 1931089 * 2 ^ 59
def prefixEnd_1931089 : Nat := 4983230072969 + 3 ^ 40 * 1931089 * 2
def baseEnd_1931089 : Nat := 661051229073533559404393

theorem tailTrace_1931089 : CollatzResearch.WordTrace tailWord_1931089 prefixEnd_1931089 661051229073533559404393 := by
  unfold tailWord_1931089
  simp only [CollatzResearch.WordTrace]
  refine ⟨70432602101001831589292321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46955068067334554392861547 70432602101001831589292321)
  ·
    refine ⟨52824451575751373691969241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70432602101001831589292321 52824451575751373691969241)
    ·
      refine ⟨39618338681813530268976931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52824451575751373691969241 39618338681813530268976931)
      ·
        refine ⟨59427508022720295403465397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39618338681813530268976931 59427508022720295403465397)
        ·
          refine ⟨5571328877130027694074881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59427508022720295403465397 5571328877130027694074881)
          ·
            refine ⟨4178496657847520770556161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571328877130027694074881 4178496657847520770556161)
            ·
              refine ⟨3133872493385640577917121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178496657847520770556161 3133872493385640577917121)
              ·
                refine ⟨2350404370039230433437841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133872493385640577917121 2350404370039230433437841)
                ·
                  refine ⟨1762803277529422825078381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2350404370039230433437841 1762803277529422825078381)
                  ·
                    refine ⟨661051229073533559404393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1762803277529422825078381 661051229073533559404393)
                    ·
                      rfl

theorem cell22_1931089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_1931089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931089 prefixEnd_1931089 := by exact prefixLift 1931089
  have htrace : WordTrace (prefixWord ++ tailWord_1931089) baseStart_1931089 baseEnd_1931089 := by
    simpa [prefixWord, tailWord_1931089, baseEnd_1931089] using wordTrace_append hprefix tailTrace_1931089
  have hstable : (prefixWord ++ tailWord_1931089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931089).length < 2 ^ (prefixWord ++ tailWord_1931089).sum := by decide
  have hdescent : baseEnd_1931089 < baseStart_1931089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931117 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1931117 : Nat := 118140960795 + 1931117 * 2 ^ 59
def prefixEnd_1931117 : Nat := 4983230072969 + 3 ^ 40 * 1931117 * 2
def baseEnd_1931117 : Nat := 661060814045750819704307

theorem tailTrace_1931117 : CollatzResearch.WordTrace tailWord_1931117 prefixEnd_1931117 661060814045750819704307 := by
  unfold tailWord_1931117
  simp only [CollatzResearch.WordTrace]
  refine ⟨70433623344900392371311605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46955748896600261580874403 70433623344900392371311605)
  ·
    refine ⟨6603152188584411784810463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70433623344900392371311605 6603152188584411784810463)
    ·
      refine ⟨9904728282876617677215695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6603152188584411784810463 9904728282876617677215695)
      ·
        refine ⟨14857092424314926515823543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904728282876617677215695 14857092424314926515823543)
        ·
          refine ⟨22285638636472389773735315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14857092424314926515823543 22285638636472389773735315)
          ·
            refine ⟨33428457954708584660602973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22285638636472389773735315 33428457954708584660602973)
            ·
              refine ⟨12535671733015719247726115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33428457954708584660602973 12535671733015719247726115)
              ·
                refine ⟨18803507599523578871589173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12535671733015719247726115 18803507599523578871589173)
                ·
                  refine ⟨1762828837455335519211485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18803507599523578871589173 1762828837455335519211485)
                  ·
                    refine ⟨661060814045750819704307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1762828837455335519211485 661060814045750819704307)
                    ·
                      rfl

theorem cell22_1931117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1931117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931117 prefixEnd_1931117 := by exact prefixLift 1931117
  have htrace : WordTrace (prefixWord ++ tailWord_1931117) baseStart_1931117 baseEnd_1931117 := by
    simpa [prefixWord, tailWord_1931117, baseEnd_1931117] using wordTrace_append hprefix tailTrace_1931117
  have hstable : (prefixWord ++ tailWord_1931117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931117).length < 2 ^ (prefixWord ++ tailWord_1931117).sum := by decide
  have hdescent : baseEnd_1931117 < baseStart_1931117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931145 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_1931145 : Nat := 118140960795 + 1931145 * 2 ^ 59
def prefixEnd_1931145 : Nat := 4983230072969 + 3 ^ 40 * 1931145 * 2
def baseEnd_1931145 : Nat := 661070399017968080004221

theorem tailTrace_1931145 : CollatzResearch.WordTrace tailWord_1931145 prefixEnd_1931145 661070399017968080004221 := by
  unfold tailWord_1931145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70434644588798953153330889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46956429725865968768887259 70434644588798953153330889)
  ·
    refine ⟨52825983441599214864998167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70434644588798953153330889 52825983441599214864998167)
    ·
      refine ⟨79238975162398822297497251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52825983441599214864998167 79238975162398822297497251)
      ·
        refine ⟨118858462743598233446245877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79238975162398822297497251 118858462743598233446245877)
        ·
          refine ⟨11142980882212334385585551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118858462743598233446245877 11142980882212334385585551)
          ·
            refine ⟨16714471323318501578378327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142980882212334385585551 16714471323318501578378327)
            ·
              refine ⟨25071706984977752367567491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16714471323318501578378327 25071706984977752367567491)
              ·
                refine ⟨37607560477466628551351237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25071706984977752367567491 37607560477466628551351237)
                ·
                  refine ⟨7051417589524992853378357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37607560477466628551351237 7051417589524992853378357)
                  ·
                    refine ⟨661070399017968080004221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7051417589524992853378357 661070399017968080004221)
                    ·
                      rfl

theorem cell22_1931145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_1931145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931145 prefixEnd_1931145 := by exact prefixLift 1931145
  have htrace : WordTrace (prefixWord ++ tailWord_1931145) baseStart_1931145 baseEnd_1931145 := by
    simpa [prefixWord, tailWord_1931145, baseEnd_1931145] using wordTrace_append hprefix tailTrace_1931145
  have hstable : (prefixWord ++ tailWord_1931145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931145).length < 2 ^ (prefixWord ++ tailWord_1931145).sum := by decide
  have hdescent : baseEnd_1931145 < baseStart_1931145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931162 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_1931162 : Nat := 118140960795 + 1931162 * 2 ^ 59
def prefixEnd_1931162 : Nat := 4983230072969 + 3 ^ 40 * 1931162 * 2
def baseEnd_1931162 : Nat := 661076218465385702329169

theorem tailTrace_1931162 : CollatzResearch.WordTrace tailWord_1931162 prefixEnd_1931162 661076218465385702329169 := by
  unfold tailWord_1931162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608816157434341264174935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46956843086491576704466493 17608816157434341264174935)
  ·
    refine ⟨26413224236151511896262403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17608816157434341264174935 26413224236151511896262403)
    ·
      refine ⟨39619836354227267844393605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26413224236151511896262403 39619836354227267844393605)
      ·
        refine ⟨7428719316417612720823801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39619836354227267844393605 7428719316417612720823801)
        ·
          refine ⟨5571539487313209540617851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7428719316417612720823801 5571539487313209540617851)
          ·
            refine ⟨8357309230969814310926777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571539487313209540617851 8357309230969814310926777)
            ·
              refine ⟨6267981923227360733195083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8357309230969814310926777 6267981923227360733195083)
              ·
                refine ⟨9401972884841041099792625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267981923227360733195083 9401972884841041099792625)
                ·
                  refine ⟨7051479663630780824844469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9401972884841041099792625 7051479663630780824844469)
                  ·
                    refine ⟨661076218465385702329169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7051479663630780824844469 661076218465385702329169)
                    ·
                      rfl

theorem cell22_1931162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_1931162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931162 prefixEnd_1931162 := by exact prefixLift 1931162
  have htrace : WordTrace (prefixWord ++ tailWord_1931162) baseStart_1931162 baseEnd_1931162 := by
    simpa [prefixWord, tailWord_1931162, baseEnd_1931162] using wordTrace_append hprefix tailTrace_1931162
  have hstable : (prefixWord ++ tailWord_1931162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931162).length < 2 ^ (prefixWord ++ tailWord_1931162).sum := by decide
  have hdescent : baseEnd_1931162 < baseStart_1931162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931205 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1931205 : Nat := 118140960795 + 1931205 * 2 ^ 59
def prefixEnd_1931205 : Nat := 4983230072969 + 3 ^ 40 * 1931205 * 2
def baseEnd_1931205 : Nat := 661090938244147923504037

theorem tailTrace_1931205 : CollatzResearch.WordTrace tailWord_1931205 prefixEnd_1931205 661090938244147923504037 := by
  unfold tailWord_1931205
  simp only [CollatzResearch.WordTrace]
  refine ⟨70436832968581583400515069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46957888645721055600343379 70436832968581583400515069)
  ·
    refine ⟨26413812363218093775193151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70436832968581583400515069 26413812363218093775193151)
    ·
      refine ⟨39620718544827140662789727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26413812363218093775193151 39620718544827140662789727)
      ·
        refine ⟨59431077817240710994184591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39620718544827140662789727 59431077817240710994184591)
        ·
          refine ⟨89146616725861066491276887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59431077817240710994184591 89146616725861066491276887)
          ·
            refine ⟨133719925088791599736915331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89146616725861066491276887 133719925088791599736915331)
            ·
              refine ⟨200579887633187399605372997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133719925088791599736915331 200579887633187399605372997)
              ·
                refine ⟨37608728931222637426007437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200579887633187399605372997 37608728931222637426007437)
                ·
                  refine ⟨14103273349208489034752789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37608728931222637426007437 14103273349208489034752789)
                  ·
                    refine ⟨661090938244147923504037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14103273349208489034752789 661090938244147923504037)
                    ·
                      rfl

theorem cell22_1931205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1931205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931205 prefixEnd_1931205 := by exact prefixLift 1931205
  have htrace : WordTrace (prefixWord ++ tailWord_1931205) baseStart_1931205 baseEnd_1931205 := by
    simpa [prefixWord, tailWord_1931205, baseEnd_1931205] using wordTrace_append hprefix tailTrace_1931205
  have hstable : (prefixWord ++ tailWord_1931205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931205).length < 2 ^ (prefixWord ++ tailWord_1931205).sum := by decide
  have hdescent : baseEnd_1931205 < baseStart_1931205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931224 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_1931224 : Nat := 118140960795 + 1931224 * 2 ^ 59
def prefixEnd_1931224 : Nat := 4983230072969 + 3 ^ 40 * 1931224 * 2
def baseEnd_1931224 : Nat := 661097442332438207278979

theorem tailTrace_1931224 : CollatzResearch.WordTrace tailWord_1931224 prefixEnd_1931224 661097442332438207278979 := by
  unfold tailWord_1931224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35218762977756374822728363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46958350637008499763637817 35218762977756374822728363)
  ·
    refine ⟨52828144466634562234092545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35218762977756374822728363 52828144466634562234092545)
    ·
      refine ⟨39621108349975921675569409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52828144466634562234092545 39621108349975921675569409)
      ·
        refine ⟨29715831262481941256677057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39621108349975921675569409 29715831262481941256677057)
        ·
          refine ⟨22286873446861455942507793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29715831262481941256677057 22286873446861455942507793)
          ·
            refine ⟨16715155085146091956880845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22286873446861455942507793 16715155085146091956880845)
            ·
              refine ⟨6268183156929784483830317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16715155085146091956880845 6268183156929784483830317)
              ·
                refine ⟨2350568683848669181436369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6268183156929784483830317 2350568683848669181436369)
                ·
                  refine ⟨1762926512886501886077277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2350568683848669181436369 1762926512886501886077277)
                  ·
                    refine ⟨661097442332438207278979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1762926512886501886077277 661097442332438207278979)
                    ·
                      rfl

theorem cell22_1931224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_1931224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931224 prefixEnd_1931224 := by exact prefixLift 1931224
  have htrace : WordTrace (prefixWord ++ tailWord_1931224) baseStart_1931224 baseEnd_1931224 := by
    simpa [prefixWord, tailWord_1931224, baseEnd_1931224] using wordTrace_append hprefix tailTrace_1931224
  have hstable : (prefixWord ++ tailWord_1931224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931224).length < 2 ^ (prefixWord ++ tailWord_1931224).sum := by decide
  have hdescent : baseEnd_1931224 < baseStart_1931224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931228 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1931228 : Nat := 118140960795 + 1931228 * 2 ^ 59
def prefixEnd_1931228 : Nat := 4983230072969 + 3 ^ 40 * 1931228 * 2
def baseEnd_1931228 : Nat := 661098811614183530178967

theorem tailTrace_1931228 : CollatzResearch.WordTrace tailWord_1931228 prefixEnd_1931228 661098811614183530178967 := by
  unfold tailWord_1931228
  simp only [CollatzResearch.WordTrace]
  refine ⟨35218835923749129164301169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46958447898332172219068225 35218835923749129164301169)
  ·
    refine ⟨26414126942811846873225877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35218835923749129164301169 26414126942811846873225877)
    ·
      refine ⟨1238162200444305322182463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26414126942811846873225877 1238162200444305322182463)
      ·
        refine ⟨1857243300666457983273695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238162200444305322182463 1857243300666457983273695)
        ·
          refine ⟨2785864950999686974910543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857243300666457983273695 2785864950999686974910543)
          ·
            refine ⟨4178797426499530462365815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785864950999686974910543 4178797426499530462365815)
            ·
              refine ⟨6268196139749295693548723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178797426499530462365815 6268196139749295693548723)
              ·
                refine ⟨9402294209623943540323085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268196139749295693548723 9402294209623943540323085)
                ·
                  refine ⟨3525860328608978827621157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9402294209623943540323085 3525860328608978827621157)
                  ·
                    refine ⟨661098811614183530178967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525860328608978827621157 661098811614183530178967)
                    ·
                      rfl

theorem cell22_1931228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1931228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931228 prefixEnd_1931228 := by exact prefixLift 1931228
  have htrace : WordTrace (prefixWord ++ tailWord_1931228) baseStart_1931228 baseEnd_1931228 := by
    simpa [prefixWord, tailWord_1931228, baseEnd_1931228] using wordTrace_append hprefix tailTrace_1931228
  have hstable : (prefixWord ++ tailWord_1931228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931228).length < 2 ^ (prefixWord ++ tailWord_1931228).sum := by decide
  have hdescent : baseEnd_1931228 < baseStart_1931228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931254 : List Nat := [5, 1, 1, 1, 5, 9]
def baseStart_1931254 : Nat := 118140960795 + 1931254 * 2 ^ 59
def prefixEnd_1931254 : Nat := 4983230072969 + 3 ^ 40 * 1931254 * 2
def baseEnd_1931254 : Nat := 8161823604265779370727

theorem tailTrace_1931254 : CollatzResearch.WordTrace tailWord_1931254 prefixEnd_1931254 8161823604265779370727 := by
  unfold tailWord_1931254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402413759087754048065551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46959080096936043179365877 4402413759087754048065551)
  ·
    refine ⟨6603620638631631072098327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4402413759087754048065551 6603620638631631072098327)
    ·
      refine ⟨9905430957947446608147491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6603620638631631072098327 9905430957947446608147491)
      ·
        refine ⟨14858146436921169912221237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9905430957947446608147491 14858146436921169912221237)
        ·
          refine ⟨1392951228461359679270741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14858146436921169912221237 1392951228461359679270741)
          ·
            refine ⟨8161823604265779370727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1392951228461359679270741 8161823604265779370727)
            ·
              rfl

theorem cell22_1931254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 9].length) (baseStart_1931254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931254 prefixEnd_1931254 := by exact prefixLift 1931254
  have htrace : WordTrace (prefixWord ++ tailWord_1931254) baseStart_1931254 baseEnd_1931254 := by
    simpa [prefixWord, tailWord_1931254, baseEnd_1931254] using wordTrace_append hprefix tailTrace_1931254
  have hstable : (prefixWord ++ tailWord_1931254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931254).length < 2 ^ (prefixWord ++ tailWord_1931254).sum := by decide
  have hdescent : baseEnd_1931254 < baseStart_1931254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931316 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1931316 : Nat := 118140960795 + 1931316 * 2 ^ 59
def prefixEnd_1931316 : Nat := 4983230072969 + 3 ^ 40 * 1931316 * 2
def baseEnd_1931316 : Nat := 220376311937526877992899

theorem tailTrace_1931316 : CollatzResearch.WordTrace tailWord_1931316 prefixEnd_1931316 220376311937526877992899 := by
  unfold tailWord_1931316
  simp only [CollatzResearch.WordTrace]
  refine ⟨35220440735589724678902901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46960587647452966238537201 35220440735589724678902901)
  ·
    refine ⟨3301916318961536688647147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35220440735589724678902901 3301916318961536688647147)
    ·
      refine ⟨4952874478442305032970721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301916318961536688647147 4952874478442305032970721)
      ·
        refine ⟨3714655858831728774728041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4952874478442305032970721 3714655858831728774728041)
        ·
          refine ⟨2785991894123796581046031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3714655858831728774728041 2785991894123796581046031)
          ·
            refine ⟨4178987841185694871569047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785991894123796581046031 4178987841185694871569047)
            ·
              refine ⟨6268481761778542307353571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178987841185694871569047 6268481761778542307353571)
              ·
                refine ⟨9402722642667813461030357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268481761778542307353571 9402722642667813461030357)
                ·
                  refine ⟨220376311937526877992899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9402722642667813461030357 220376311937526877992899)
                  ·
                    rfl

theorem cell22_1931316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1931316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931316 prefixEnd_1931316 := by exact prefixLift 1931316
  have htrace : WordTrace (prefixWord ++ tailWord_1931316) baseStart_1931316 baseEnd_1931316 := by
    simpa [prefixWord, tailWord_1931316, baseEnd_1931316] using wordTrace_append hprefix tailTrace_1931316
  have hstable : (prefixWord ++ tailWord_1931316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931316).length < 2 ^ (prefixWord ++ tailWord_1931316).sum := by decide
  have hdescent : baseEnd_1931316 < baseStart_1931316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931327 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 6]
def baseStart_1931327 : Nat := 118140960795 + 1931327 * 2 ^ 59
def prefixEnd_1931327 : Nat := 4983230072969 + 3 ^ 40 * 1931327 * 2
def baseEnd_1931327 : Nat := 220377567112460090651221

theorem tailTrace_1931327 : CollatzResearch.WordTrace tailWord_1931327 prefixEnd_1931327 220377567112460090651221 := by
  unfold tailWord_1931327
  simp only [CollatzResearch.WordTrace]
  refine ⟨70441282674139598236456235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46960855116093065490970823 70441282674139598236456235)
  ·
    refine ⟨105661924011209397354684353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70441282674139598236456235 105661924011209397354684353)
    ·
      refine ⟨79246443008407048016013265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105661924011209397354684353 79246443008407048016013265)
      ·
        refine ⟨59434832256305286012009949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79246443008407048016013265 59434832256305286012009949)
        ·
          refine ⟨22288062096114482254503731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59434832256305286012009949 22288062096114482254503731)
          ·
            refine ⟨33432093144171723381755597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22288062096114482254503731 33432093144171723381755597)
            ·
              refine ⟨12537034929064396268158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33432093144171723381755597 12537034929064396268158349)
              ·
                refine ⟨4701388098399148600559381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12537034929064396268158349 4701388098399148600559381)
                ·
                  refine ⟨220377567112460090651221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4701388098399148600559381 220377567112460090651221)
                  ·
                    rfl

theorem cell22_1931327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 6].length) (baseStart_1931327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931327 prefixEnd_1931327 := by exact prefixLift 1931327
  have htrace : WordTrace (prefixWord ++ tailWord_1931327) baseStart_1931327 baseEnd_1931327 := by
    simpa [prefixWord, tailWord_1931327, baseEnd_1931327] using wordTrace_append hprefix tailTrace_1931327
  have hstable : (prefixWord ++ tailWord_1931327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931327).length < 2 ^ (prefixWord ++ tailWord_1931327).sum := by decide
  have hdescent : baseEnd_1931327 < baseStart_1931327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931372 : List Nat := [2, 2, 1, 1, 3, 3, 10]
def baseStart_1931372 : Nat := 118140960795 + 1931372 * 2 ^ 59
def prefixEnd_1931372 : Nat := 4983230072969 + 3 ^ 40 * 1931372 * 2
def baseEnd_1931372 : Nat := 24486966879889450169575

theorem tailTrace_1931372 : CollatzResearch.WordTrace tailWord_1931372 prefixEnd_1931372 24486966879889450169575 := by
  unfold tailWord_1931372
  simp only [CollatzResearch.WordTrace]
  refine ⟨35221461979488285460922185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46961949305984380614562913 35221461979488285460922185)
  ·
    refine ⟨26416096484616214095691639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35221461979488285460922185 26416096484616214095691639)
    ·
      refine ⟨39624144726924321143537459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26416096484616214095691639 39624144726924321143537459)
      ·
        refine ⟨59436217090386481715306189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39624144726924321143537459 59436217090386481715306189)
        ·
          refine ⟨22288581408894930643239821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59436217090386481715306189 22288581408894930643239821)
          ·
            refine ⟨8358218028335598991214933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22288581408894930643239821 8358218028335598991214933)
            ·
              refine ⟨24486966879889450169575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8358218028335598991214933 24486966879889450169575)
              ·
                rfl

theorem cell22_1931372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 10].length) (baseStart_1931372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931372 prefixEnd_1931372 := by exact prefixLift 1931372
  have htrace : WordTrace (prefixWord ++ tailWord_1931372) baseStart_1931372 baseEnd_1931372 := by
    simpa [prefixWord, tailWord_1931372, baseEnd_1931372] using wordTrace_append hprefix tailTrace_1931372
  have hstable : (prefixWord ++ tailWord_1931372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931372).length < 2 ^ (prefixWord ++ tailWord_1931372).sum := by decide
  have hdescent : baseEnd_1931372 < baseStart_1931372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931378 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1931378 : Nat := 118140960795 + 1931378 * 2 ^ 59
def prefixEnd_1931378 : Nat := 4983230072969 + 3 ^ 40 * 1931378 * 2
def baseEnd_1931378 : Nat := 220383386559877712976169

theorem tailTrace_1931378 : CollatzResearch.WordTrace tailWord_1931378 prefixEnd_1931378 220383386559877712976169 := by
  unfold tailWord_1931378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17610785699238708486640697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46962095197969889297708525 17610785699238708486640697)
  ·
    refine ⟨13208089274429031364980523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17610785699238708486640697 13208089274429031364980523)
    ·
      refine ⟨19812133911643547047470785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13208089274429031364980523 19812133911643547047470785)
      ·
        refine ⟨14859100433732660285603089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19812133911643547047470785 14859100433732660285603089)
        ·
          refine ⟨11144325325299495214202317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14859100433732660285603089 11144325325299495214202317)
          ·
            refine ⟨4179121996987310705325869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11144325325299495214202317 4179121996987310705325869)
            ·
              refine ⟨1567170748870241514497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4179121996987310705325869 1567170748870241514497201)
              ·
                refine ⟨1175378061652681135872901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567170748870241514497201 1175378061652681135872901)
                ·
                  refine ⟨220383386559877712976169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1175378061652681135872901 220383386559877712976169)
                  ·
                    rfl

theorem cell22_1931378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1931378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931378 prefixEnd_1931378 := by exact prefixLift 1931378
  have htrace : WordTrace (prefixWord ++ tailWord_1931378) baseStart_1931378 baseEnd_1931378 := by
    simpa [prefixWord, tailWord_1931378, baseEnd_1931378] using wordTrace_append hprefix tailTrace_1931378
  have hstable : (prefixWord ++ tailWord_1931378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931378).length < 2 ^ (prefixWord ++ tailWord_1931378).sum := by decide
  have hdescent : baseEnd_1931378 < baseStart_1931378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931389 : List Nat := [1, 4, 1, 1, 3, 3, 2, 7]
def baseStart_1931389 : Nat := 118140960795 + 1931389 * 2 ^ 59
def prefixEnd_1931389 : Nat := 4983230072969 + 3 ^ 40 * 1931389 * 2
def baseEnd_1931389 : Nat := 73461547244936975211497

theorem tailTrace_1931389 : CollatzResearch.WordTrace tailWord_1931389 prefixEnd_1931389 73461547244936975211497 := by
  unfold tailWord_1931389
  simp only [CollatzResearch.WordTrace]
  refine ⟨70443543999914982825213221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46962362666609988550142147 70443543999914982825213221)
  ·
    refine ⟨13208164499984059279727479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70443543999914982825213221 13208164499984059279727479)
    ·
      refine ⟨19812246749976088919591219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13208164499984059279727479 19812246749976088919591219)
      ·
        refine ⟨29718370124964133379386829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19812246749976088919591219 29718370124964133379386829)
        ·
          refine ⟨11144388796861550017270061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29718370124964133379386829 11144388796861550017270061)
          ·
            refine ⟨4179145798823081256476273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11144388796861550017270061 4179145798823081256476273)
            ·
              refine ⟨3134359349117310942357205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179145798823081256476273 3134359349117310942357205)
              ·
                refine ⟨73461547244936975211497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3134359349117310942357205 73461547244936975211497)
                ·
                  rfl

theorem cell22_1931389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 7].length) (baseStart_1931389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931389 prefixEnd_1931389 := by exact prefixLift 1931389
  have htrace : WordTrace (prefixWord ++ tailWord_1931389) baseStart_1931389 baseEnd_1931389 := by
    simpa [prefixWord, tailWord_1931389, baseEnd_1931389] using wordTrace_append hprefix tailTrace_1931389
  have hstable : (prefixWord ++ tailWord_1931389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931389).length < 2 ^ (prefixWord ++ tailWord_1931389).sum := by decide
  have hdescent : baseEnd_1931389 < baseStart_1931389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931393 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1931393 : Nat := 118140960795 + 1931393 * 2 ^ 59
def prefixEnd_1931393 : Nat := 4983230072969 + 3 ^ 40 * 1931393 * 2
def baseEnd_1931393 : Nat := 661155294486178099803461

theorem tailTrace_1931393 : CollatzResearch.WordTrace tailWord_1931393 prefixEnd_1931393 661155294486178099803461 := by
  unfold tailWord_1931393
  simp only [CollatzResearch.WordTrace]
  refine ⟨70443689891900491508358833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46962459927933661005572555 70443689891900491508358833)
  ·
    refine ⟨52832767418925368631269125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70443689891900491508358833 52832767418925368631269125)
    ·
      refine ⟨9906143891048506618362961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52832767418925368631269125 9906143891048506618362961)
      ·
        refine ⟨7429607918286379963772221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9906143891048506618362961 7429607918286379963772221)
        ·
          refine ⟨2786102969357392486414583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7429607918286379963772221 2786102969357392486414583)
          ·
            refine ⟨4179154454036088729621875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786102969357392486414583 4179154454036088729621875)
            ·
              refine ⟨6268731681054133094432813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179154454036088729621875 6268731681054133094432813)
              ·
                refine ⟨2350774380395299910412305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6268731681054133094432813 2350774380395299910412305)
                ·
                  refine ⟨1763080785296474932809229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2350774380395299910412305 1763080785296474932809229)
                  ·
                    refine ⟨661155294486178099803461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763080785296474932809229 661155294486178099803461)
                    ·
                      rfl

theorem cell22_1931393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1931393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931393 prefixEnd_1931393 := by exact prefixLift 1931393
  have htrace : WordTrace (prefixWord ++ tailWord_1931393) baseStart_1931393 baseEnd_1931393 := by
    simpa [prefixWord, tailWord_1931393, baseEnd_1931393] using wordTrace_append hprefix tailTrace_1931393
  have hstable : (prefixWord ++ tailWord_1931393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931393).length < 2 ^ (prefixWord ++ tailWord_1931393).sum := by decide
  have hdescent : baseEnd_1931393 < baseStart_1931393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931417 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 9]
def baseStart_1931417 : Nat := 118140960795 + 1931417 * 2 ^ 59
def prefixEnd_1931417 : Nat := 4983230072969 + 3 ^ 40 * 1931417 * 2
def baseEnd_1931417 : Nat := 220387836725550012401129

theorem tailTrace_1931417 : CollatzResearch.WordTrace tailWord_1931417 prefixEnd_1931417 220387836725550012401129 := by
  unfold tailWord_1931417
  simp only [CollatzResearch.WordTrace]
  refine ⟨70444565243813543607232505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46963043495875695738155003 70444565243813543607232505)
  ·
    refine ⟨52833423932860157705424379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70444565243813543607232505 52833423932860157705424379)
    ·
      refine ⟨79250135899290236558136569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52833423932860157705424379 79250135899290236558136569)
      ·
        refine ⟨59437601924467677418602427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79250135899290236558136569 59437601924467677418602427)
        ·
          refine ⟨89156402886701516127903641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59437601924467677418602427 89156402886701516127903641)
          ·
            refine ⟨66867302165026137095927731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89156402886701516127903641 66867302165026137095927731)
            ·
              refine ⟨100300953247539205643891597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66867302165026137095927731 100300953247539205643891597)
              ·
                refine ⟨37612857467827202116459349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100300953247539205643891597 37612857467827202116459349)
                ·
                  refine ⟨220387836725550012401129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37612857467827202116459349 220387836725550012401129)
                  ·
                    rfl

theorem cell22_1931417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_1931417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931417 prefixEnd_1931417 := by exact prefixLift 1931417
  have htrace : WordTrace (prefixWord ++ tailWord_1931417) baseStart_1931417 baseEnd_1931417 := by
    simpa [prefixWord, tailWord_1931417, baseEnd_1931417] using wordTrace_append hprefix tailTrace_1931417
  have hstable : (prefixWord ++ tailWord_1931417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931417).length < 2 ^ (prefixWord ++ tailWord_1931417).sum := by decide
  have hdescent : baseEnd_1931417 < baseStart_1931417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931449 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_1931449 : Nat := 118140960795 + 1931449 * 2 ^ 59
def prefixEnd_1931449 : Nat := 4983230072969 + 3 ^ 40 * 1931449 * 2
def baseEnd_1931449 : Nat := 661174464430612620403289

theorem tailTrace_1931449 : CollatzResearch.WordTrace tailWord_1931449 prefixEnd_1931449 661174464430612620403289 := by
  unfold tailWord_1931449
  simp only [CollatzResearch.WordTrace]
  refine ⟨70445732379697613072397401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46963821586465075381598267 70445732379697613072397401)
  ·
    refine ⟨52834299284773209804298051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70445732379697613072397401 52834299284773209804298051)
    ·
      refine ⟨79251448927159814706447077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52834299284773209804298051 79251448927159814706447077)
      ·
        refine ⟨14859646673842465257458827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79251448927159814706447077 14859646673842465257458827)
        ·
          refine ⟨22289470010763697886188241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14859646673842465257458827 22289470010763697886188241)
          ·
            refine ⟨16717102508072773414641181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22289470010763697886188241 16717102508072773414641181)
            ·
              refine ⟨6268913440527290030490443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16717102508072773414641181 6268913440527290030490443)
              ·
                refine ⟨9403370160790935045735665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268913440527290030490443 9403370160790935045735665)
                ·
                  refine ⟨7052527620593201284301749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403370160790935045735665 7052527620593201284301749)
                  ·
                    refine ⟨661174464430612620403289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7052527620593201284301749 661174464430612620403289)
                    ·
                      rfl

theorem cell22_1931449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_1931449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931449 prefixEnd_1931449 := by exact prefixLift 1931449
  have htrace : WordTrace (prefixWord ++ tailWord_1931449) baseStart_1931449 baseEnd_1931449 := by
    simpa [prefixWord, tailWord_1931449, baseEnd_1931449] using wordTrace_append hprefix tailTrace_1931449
  have hstable : (prefixWord ++ tailWord_1931449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931449).length < 2 ^ (prefixWord ++ tailWord_1931449).sum := by decide
  have hdescent : baseEnd_1931449 < baseStart_1931449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931496 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_1931496 : Nat := 118140960795 + 1931496 * 2 ^ 59
def prefixEnd_1931496 : Nat := 4983230072969 + 3 ^ 40 * 1931496 * 2
def baseEnd_1931496 : Nat := 220396851163706721492715

theorem tailTrace_1931496 : CollatzResearch.WordTrace tailWord_1931496 prefixEnd_1931496 220396851163706721492715 := by
  unfold tailWord_1931496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223723305263670049679171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46964964407018226732905561 35223723305263670049679171)
  ·
    refine ⟨52835584957895505074518757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35223723305263670049679171 52835584957895505074518757)
    ·
      refine ⟨9906672179605407201472267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52835584957895505074518757 9906672179605407201472267)
      ·
        refine ⟨14860008269408110802208401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906672179605407201472267 14860008269408110802208401)
        ·
          refine ⟨11145006202056083101656301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14860008269408110802208401 11145006202056083101656301)
          ·
            refine ⟨4179377325771031163121113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11145006202056083101656301 4179377325771031163121113)
            ·
              refine ⟨3134532994328273372340835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179377325771031163121113 3134532994328273372340835)
              ·
                refine ⟨4701799491492410058511253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134532994328273372340835 4701799491492410058511253)
                ·
                  refine ⟨220396851163706721492715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4701799491492410058511253 220396851163706721492715)
                  ·
                    rfl

theorem cell22_1931496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_1931496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931496 prefixEnd_1931496 := by exact prefixLift 1931496
  have htrace : WordTrace (prefixWord ++ tailWord_1931496) baseStart_1931496 baseEnd_1931496 := by
    simpa [prefixWord, tailWord_1931496, baseEnd_1931496] using wordTrace_append hprefix tailTrace_1931496
  have hstable : (prefixWord ++ tailWord_1931496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931496).length < 2 ^ (prefixWord ++ tailWord_1931496).sum := by decide
  have hdescent : baseEnd_1931496 < baseStart_1931496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931584 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_1931584 : Nat := 118140960795 + 1931584 * 2 ^ 59
def prefixEnd_1931584 : Nat := 4983230072969 + 3 ^ 40 * 1931584 * 2
def baseEnd_1931584 : Nat := 661220677689517268277875

theorem tailTrace_1931584 : CollatzResearch.WordTrace tailWord_1931584 prefixEnd_1931584 661220677689517268277875 := by
  unfold tailWord_1931584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35225328117104265564280903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46967104156139020752374537 35225328117104265564280903)
  ·
    refine ⟨52837992175656398346421355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35225328117104265564280903 52837992175656398346421355)
    ·
      refine ⟨79256988263484597519632033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52837992175656398346421355 79256988263484597519632033)
      ·
        refine ⟨59442741197613448139724025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79256988263484597519632033 59442741197613448139724025)
        ·
          refine ⟨44582055898210086104793019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59442741197613448139724025 44582055898210086104793019)
          ·
            refine ⟨66873083847315129157189529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44582055898210086104793019 66873083847315129157189529)
            ·
              refine ⟨50154812885486346867892147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66873083847315129157189529 50154812885486346867892147)
              ·
                refine ⟨75232219328229520301838221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50154812885486346867892147 75232219328229520301838221)
                ·
                  refine ⟨28212082248086070113189333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75232219328229520301838221 28212082248086070113189333)
                  ·
                    refine ⟨661220677689517268277875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28212082248086070113189333 661220677689517268277875)
                    ·
                      rfl

theorem cell22_1931584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_1931584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931584 prefixEnd_1931584 := by exact prefixLift 1931584
  have htrace : WordTrace (prefixWord ++ tailWord_1931584) baseStart_1931584 baseEnd_1931584 := by
    simpa [prefixWord, tailWord_1931584, baseEnd_1931584] using wordTrace_append hprefix tailTrace_1931584
  have hstable : (prefixWord ++ tailWord_1931584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931584).length < 2 ^ (prefixWord ++ tailWord_1931584).sum := by decide
  have hdescent : baseEnd_1931584 < baseStart_1931584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931618 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1931618 : Nat := 118140960795 + 1931618 * 2 ^ 59
def prefixEnd_1931618 : Nat := 4983230072969 + 3 ^ 40 * 1931618 * 2
def baseEnd_1931618 : Nat := 661232316584352512927771

theorem tailTrace_1931618 : CollatzResearch.WordTrace tailWord_1931618 prefixEnd_1931618 661232316584352512927771 := by
  unfold tailWord_1931618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17612974079021338733824877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46967930877390236623533005 17612974079021338733824877)
  ·
    refine ⟨6604865279633002025184329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17612974079021338733824877 6604865279633002025184329)
    ·
      refine ⟨4953648959724751518888247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6604865279633002025184329 4953648959724751518888247)
      ·
        refine ⟨7430473439587127278332371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4953648959724751518888247 7430473439587127278332371)
        ·
          refine ⟨11145710159380690917498557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7430473439587127278332371 11145710159380690917498557)
          ·
            refine ⟨4179641309767759094061959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11145710159380690917498557 4179641309767759094061959)
            ·
              refine ⟨6269461964651638641092939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179641309767759094061959 6269461964651638641092939)
              ·
                refine ⟨9404192946977457961639409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269461964651638641092939 9404192946977457961639409)
                ·
                  refine ⟨7053144710233093471229557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9404192946977457961639409 7053144710233093471229557)
                  ·
                    refine ⟨661232316584352512927771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7053144710233093471229557 661232316584352512927771)
                    ·
                      rfl

theorem cell22_1931618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1931618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931618 prefixEnd_1931618 := by exact prefixLift 1931618
  have htrace : WordTrace (prefixWord ++ tailWord_1931618) baseStart_1931618 baseEnd_1931618 := by
    simpa [prefixWord, tailWord_1931618, baseEnd_1931618] using wordTrace_append hprefix tailTrace_1931618
  have hstable : (prefixWord ++ tailWord_1931618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931618).length < 2 ^ (prefixWord ++ tailWord_1931618).sum := by decide
  have hdescent : baseEnd_1931618 < baseStart_1931618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931721 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 7]
def baseStart_1931721 : Nat := 118140960795 + 1931721 * 2 ^ 59
def prefixEnd_1931721 : Nat := 4983230072969 + 3 ^ 40 * 1931721 * 2
def baseEnd_1931721 : Nat := 220422525196431525867485

theorem tailTrace_1931721 : CollatzResearch.WordTrace tailWord_1931721 prefixEnd_1931721 220422525196431525867485 := by
  unfold tailWord_1931721
  simp only [CollatzResearch.WordTrace]
  refine ⟨70455653034712203526299017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46970435356474802350866011 70455653034712203526299017)
  ·
    refine ⟨52841739776034152644724263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70455653034712203526299017 52841739776034152644724263)
    ·
      refine ⟨79262609664051228967086395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52841739776034152644724263 79262609664051228967086395)
      ·
        refine ⟨118893914496076843450629593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79262609664051228967086395 118893914496076843450629593)
        ·
          refine ⟨89170435872057632587972195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118893914496076843450629593 89170435872057632587972195)
          ·
            refine ⟨133755653808086448881958293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89170435872057632587972195 133755653808086448881958293)
            ·
              refine ⟨6269796272254052291341795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133755653808086448881958293 6269796272254052291341795)
              ·
                refine ⟨9404694408381078437012693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269796272254052291341795 9404694408381078437012693)
                ·
                  refine ⟨220422525196431525867485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9404694408381078437012693 220422525196431525867485)
                  ·
                    rfl

theorem cell22_1931721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_1931721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931721 prefixEnd_1931721 := by exact prefixLift 1931721
  have htrace : WordTrace (prefixWord ++ tailWord_1931721) baseStart_1931721 baseEnd_1931721 := by
    simpa [prefixWord, tailWord_1931721, baseEnd_1931721] using wordTrace_append hprefix tailTrace_1931721
  have hstable : (prefixWord ++ tailWord_1931721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931721).length < 2 ^ (prefixWord ++ tailWord_1931721).sum := by decide
  have hdescent : baseEnd_1931721 < baseStart_1931721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931736 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_1931736 : Nat := 118140960795 + 1931736 * 2 ^ 59
def prefixEnd_1931736 : Nat := 4983230072969 + 3 ^ 40 * 1931736 * 2
def baseEnd_1931736 : Nat := 661272710395839538477409

theorem tailTrace_1931736 : CollatzResearch.WordTrace tailWord_1931736 prefixEnd_1931736 661272710395839538477409 := by
  unfold tailWord_1931736
  simp only [CollatzResearch.WordTrace]
  refine ⟨35228100064828930544047531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46970800086438574058730041 35228100064828930544047531)
  ·
    refine ⟨52842150097243395816071297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35228100064828930544047531 52842150097243395816071297)
    ·
      refine ⟨39631612572932546862053473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52842150097243395816071297 39631612572932546862053473)
      ·
        refine ⟨29723709429699410146540105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39631612572932546862053473 29723709429699410146540105)
        ·
          refine ⟨22292782072274557609905079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29723709429699410146540105 22292782072274557609905079)
          ·
            refine ⟨33439173108411836414857619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22292782072274557609905079 33439173108411836414857619)
            ·
              refine ⟨50158759662617754622286429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33439173108411836414857619 50158759662617754622286429)
              ·
                refine ⟨18809534873481657983357411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50158759662617754622286429 18809534873481657983357411)
                ·
                  refine ⟨28214302310222486975036117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18809534873481657983357411 28214302310222486975036117)
                  ·
                    refine ⟨661272710395839538477409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28214302310222486975036117 661272710395839538477409)
                    ·
                      rfl

theorem cell22_1931736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_1931736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931736 prefixEnd_1931736 := by exact prefixLift 1931736
  have htrace : WordTrace (prefixWord ++ tailWord_1931736) baseStart_1931736 baseEnd_1931736 := by
    simpa [prefixWord, tailWord_1931736, baseEnd_1931736] using wordTrace_append hprefix tailTrace_1931736
  have hstable : (prefixWord ++ tailWord_1931736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931736).length < 2 ^ (prefixWord ++ tailWord_1931736).sum := by decide
  have hdescent : baseEnd_1931736 < baseStart_1931736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931738 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_1931738 : Nat := 118140960795 + 1931738 * 2 ^ 59
def prefixEnd_1931738 : Nat := 4983230072969 + 3 ^ 40 * 1931738 * 2
def baseEnd_1931738 : Nat := 220424465012237399975801

theorem tailTrace_1931738 : CollatzResearch.WordTrace tailWord_1931738 prefixEnd_1931738 220424465012237399975801 := by
  unfold tailWord_1931738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17614068268912653857416967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46970848717100410286445245 17614068268912653857416967)
  ·
    refine ⟨26421102403368980786125451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17614068268912653857416967 26421102403368980786125451)
    ·
      refine ⟨39631653605053471179188177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26421102403368980786125451 39631653605053471179188177)
      ·
        refine ⟨29723740203790103384391133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39631653605053471179188177 29723740203790103384391133)
        ·
          refine ⟨11146402576421288769146675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29723740203790103384391133 11146402576421288769146675)
          ·
            refine ⟨16719603864631933153720013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11146402576421288769146675 16719603864631933153720013)
            ·
              refine ⟨6269851449236974932645005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16719603864631933153720013 6269851449236974932645005)
              ·
                refine ⟨2351194293463865599741877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6269851449236974932645005 2351194293463865599741877)
                ·
                  refine ⟨220424465012237399975801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2351194293463865599741877 220424465012237399975801)
                  ·
                    rfl

theorem cell22_1931738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_1931738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931738 prefixEnd_1931738 := by exact prefixLift 1931738
  have htrace : WordTrace (prefixWord ++ tailWord_1931738) baseStart_1931738 baseEnd_1931738 := by
    simpa [prefixWord, tailWord_1931738, baseEnd_1931738] using wordTrace_append hprefix tailTrace_1931738
  have hstable : (prefixWord ++ tailWord_1931738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931738).length < 2 ^ (prefixWord ++ tailWord_1931738).sum := by decide
  have hdescent : baseEnd_1931738 < baseStart_1931738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931873 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 7]
def baseStart_1931873 : Nat := 118140960795 + 1931873 * 2 ^ 59
def prefixEnd_1931873 : Nat := 4983230072969 + 3 ^ 40 * 1931873 * 2
def baseEnd_1931873 : Nat := 220439869431872282600663

theorem tailTrace_1931873 : CollatzResearch.WordTrace tailWord_1931873 prefixEnd_1931873 220439869431872282600663 := by
  unfold tailWord_1931873
  simp only [CollatzResearch.WordTrace]
  refine ⟨70461196930161533485832273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46974131286774355657221515 70461196930161533485832273)
  ·
    refine ⟨52845897697621150114374205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70461196930161533485832273 52845897697621150114374205)
    ·
      refine ⟨19817211636607931292890327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52845897697621150114374205 19817211636607931292890327)
      ·
        refine ⟨29725817454911896939335491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19817211636607931292890327 29725817454911896939335491)
        ·
          refine ⟨44588726182367845409003237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29725817454911896939335491 44588726182367845409003237)
          ·
            refine ⟨8360386159193971014188107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44588726182367845409003237 8360386159193971014188107)
            ·
              refine ⟨12540579238790956521282161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360386159193971014188107 12540579238790956521282161)
              ·
                refine ⟨9405434429093217390961621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12540579238790956521282161 9405434429093217390961621)
                ·
                  refine ⟨220439869431872282600663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9405434429093217390961621 220439869431872282600663)
                  ·
                    rfl

theorem cell22_1931873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_1931873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931873 prefixEnd_1931873 := by exact prefixLift 1931873
  have htrace : WordTrace (prefixWord ++ tailWord_1931873) baseStart_1931873 baseEnd_1931873 := by
    simpa [prefixWord, tailWord_1931873, baseEnd_1931873] using wordTrace_append hprefix tailTrace_1931873
  have hstable : (prefixWord ++ tailWord_1931873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931873).length < 2 ^ (prefixWord ++ tailWord_1931873).sum := by decide
  have hdescent : baseEnd_1931873 < baseStart_1931873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931967 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 2, 3]
def baseStart_1931967 : Nat := 118140960795 + 1931967 * 2 ^ 59
def prefixEnd_1931967 : Nat := 4983230072969 + 3 ^ 40 * 1931967 * 2
def baseEnd_1931967 : Nat := 661351786416631935951701

theorem tailTrace_1931967 : CollatzResearch.WordTrace tailWord_1931967 prefixEnd_1931967 661351786416631935951701 := by
  unfold tailWord_1931967
  simp only [CollatzResearch.WordTrace]
  refine ⟨70464625391820987539754155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46976416927880658359836103 70464625391820987539754155)
  ·
    refine ⟨105696938087731481309631233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70464625391820987539754155 105696938087731481309631233)
    ·
      refine ⟨79272703565798610982223425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105696938087731481309631233 79272703565798610982223425)
      ·
        refine ⟨59454527674348958236667569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79272703565798610982223425 59454527674348958236667569)
        ·
          refine ⟨44590895755761718677500677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59454527674348958236667569 44590895755761718677500677)
          ·
            refine ⟨8360792954205322252031377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44590895755761718677500677 8360792954205322252031377)
            ·
              refine ⟨6270594715653991689023533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8360792954205322252031377 6270594715653991689023533)
              ·
                refine ⟨2351473018370246883383825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6270594715653991689023533 2351473018370246883383825)
                ·
                  refine ⟨1763604763777685162537869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351473018370246883383825 1763604763777685162537869)
                  ·
                    refine ⟨661351786416631935951701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763604763777685162537869 661351786416631935951701)
                    ·
                      rfl

theorem cell22_1931967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_1931967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931967 prefixEnd_1931967 := by exact prefixLift 1931967
  have htrace : WordTrace (prefixWord ++ tailWord_1931967) baseStart_1931967 baseEnd_1931967 := by
    simpa [prefixWord, tailWord_1931967, baseEnd_1931967] using wordTrace_append hprefix tailTrace_1931967
  have hstable : (prefixWord ++ tailWord_1931967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931967).length < 2 ^ (prefixWord ++ tailWord_1931967).sum := by decide
  have hdescent : baseEnd_1931967 < baseStart_1931967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931969 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 6]
def baseStart_1931969 : Nat := 118140960795 + 1931969 * 2 ^ 59
def prefixEnd_1931969 : Nat := 4983230072969 + 3 ^ 40 * 1931969 * 2
def baseEnd_1931969 : Nat := 220450823685834865800565

theorem tailTrace_1931969 : CollatzResearch.WordTrace tailWord_1931969 prefixEnd_1931969 220450823685834865800565 := by
  unfold tailWord_1931969
  simp only [CollatzResearch.WordTrace]
  refine ⟨70464698337813741881326961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46976465558542494587551307 70464698337813741881326961)
  ·
    refine ⟨52848523753360306410995221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70464698337813741881326961 52848523753360306410995221)
    ·
      refine ⟨2477274550938764363015401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52848523753360306410995221 2477274550938764363015401)
      ·
        refine ⟨1857955913204073272261551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477274550938764363015401 1857955913204073272261551)
        ·
          refine ⟨2786933869806109908392327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857955913204073272261551 2786933869806109908392327)
          ·
            refine ⟨4180400804709164862588491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786933869806109908392327 4180400804709164862588491)
            ·
              refine ⟨6270601207063747293882737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180400804709164862588491 6270601207063747293882737)
              ·
                refine ⟨4702950905297810470412053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270601207063747293882737 4702950905297810470412053)
                ·
                  refine ⟨220450823685834865800565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4702950905297810470412053 220450823685834865800565)
                  ·
                    rfl

theorem cell22_1931969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_1931969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931969 prefixEnd_1931969 := by exact prefixLift 1931969
  have htrace : WordTrace (prefixWord ++ tailWord_1931969) baseStart_1931969 baseEnd_1931969 := by
    simpa [prefixWord, tailWord_1931969, baseEnd_1931969] using wordTrace_append hprefix tailTrace_1931969
  have hstable : (prefixWord ++ tailWord_1931969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931969).length < 2 ^ (prefixWord ++ tailWord_1931969).sum := by decide
  have hdescent : baseEnd_1931969 < baseStart_1931969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931982 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1931982 : Nat := 118140960795 + 1931982 * 2 ^ 59
def prefixEnd_1931982 : Nat := 4983230072969 + 3 ^ 40 * 1931982 * 2
def baseEnd_1931982 : Nat := 661356921223176896826655

theorem tailTrace_1931982 : CollatzResearch.WordTrace tailWord_1931982 prefixEnd_1931982 661356921223176896826655 := by
  unfold tailWord_1931982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808146560845830637693775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46976781657844430067700133 8808146560845830637693775)
  ·
    refine ⟨13212219841268745956540663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8808146560845830637693775 13212219841268745956540663)
    ·
      refine ⟨19818329761903118934810995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13212219841268745956540663 19818329761903118934810995)
      ·
        refine ⟨29727494642854678402216493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19818329761903118934810995 29727494642854678402216493)
        ·
          refine ⟨11147810491070504400831185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29727494642854678402216493 11147810491070504400831185)
          ·
            refine ⟨8360857868302878300623389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11147810491070504400831185 8360857868302878300623389)
            ·
              refine ⟨3135321700613579362733771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8360857868302878300623389 3135321700613579362733771)
              ·
                refine ⟨4702982550920369044100657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135321700613579362733771 4702982550920369044100657)
                ·
                  refine ⟨3527236913190276783075493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702982550920369044100657 3527236913190276783075493)
                  ·
                    refine ⟨661356921223176896826655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527236913190276783075493 661356921223176896826655)
                    ·
                      rfl

theorem cell22_1931982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1931982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931982 prefixEnd_1931982 := by exact prefixLift 1931982
  have htrace : WordTrace (prefixWord ++ tailWord_1931982) baseStart_1931982 baseEnd_1931982 := by
    simpa [prefixWord, tailWord_1931982, baseEnd_1931982] using wordTrace_append hprefix tailTrace_1931982
  have hstable : (prefixWord ++ tailWord_1931982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931982).length < 2 ^ (prefixWord ++ tailWord_1931982).sum := by decide
  have hdescent : baseEnd_1931982 < baseStart_1931982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931988 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_1931988 : Nat := 118140960795 + 1931988 * 2 ^ 59
def prefixEnd_1931988 : Nat := 4983230072969 + 3 ^ 40 * 1931988 * 2
def baseEnd_1931988 : Nat := 661358975145794881176637

theorem tailTrace_1931988 : CollatzResearch.WordTrace tailWord_1931988 prefixEnd_1931988 661358975145794881176637 := by
  unfold tailWord_1931988
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232695662372454063134309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46976927549829938750845745 35232695662372454063134309)
  ·
    refine ⟨6606130436694835136837683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35232695662372454063134309 6606130436694835136837683)
    ·
      refine ⟨9909195655042252705256525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606130436694835136837683 9909195655042252705256525)
      ·
        refine ⟨3715948370640844764471197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9909195655042252705256525 3715948370640844764471197)
        ·
          refine ⟨1393480638990316786676699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3715948370640844764471197 1393480638990316786676699)
          ·
            refine ⟨2090220958485475180015049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393480638990316786676699 2090220958485475180015049)
            ·
              refine ⟨1567665718864106385011287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090220958485475180015049 1567665718864106385011287)
              ·
                refine ⟨2351498578296159577516931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567665718864106385011287 2351498578296159577516931)
                ·
                  refine ⟨3527247867444239366275397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351498578296159577516931 3527247867444239366275397)
                  ·
                    refine ⟨661358975145794881176637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527247867444239366275397 661358975145794881176637)
                    ·
                      rfl

theorem cell22_1931988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_1931988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1931988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1931988 prefixEnd_1931988 := by exact prefixLift 1931988
  have htrace : WordTrace (prefixWord ++ tailWord_1931988) baseStart_1931988 baseEnd_1931988 := by
    simpa [prefixWord, tailWord_1931988, baseEnd_1931988] using wordTrace_append hprefix tailTrace_1931988
  have hstable : (prefixWord ++ tailWord_1931988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931988).length < 2 ^ (prefixWord ++ tailWord_1931988).sum := by decide
  have hdescent : baseEnd_1931988 < baseStart_1931988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932025 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 5]
def baseStart_1932025 : Nat := 118140960795 + 1932025 * 2 ^ 59
def prefixEnd_1932025 : Nat := 4983230072969 + 3 ^ 40 * 1932025 * 2
def baseEnd_1932025 : Nat := 220457213667313039333841

theorem tailTrace_1932025 : CollatzResearch.WordTrace tailWord_1932025 prefixEnd_1932025 220457213667313039333841 := by
  unfold tailWord_1932025
  simp only [CollatzResearch.WordTrace]
  refine ⟨70466740825610863445365529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46977827217073908963577019 70466740825610863445365529)
  ·
    refine ⟨52850055619208147584024147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70466740825610863445365529 52850055619208147584024147)
    ·
      refine ⟨79275083428812221376036221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52850055619208147584024147 79275083428812221376036221)
      ·
        refine ⟨29728156285804583016013583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79275083428812221376036221 29728156285804583016013583)
        ·
          refine ⟨44592234428706874524020375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29728156285804583016013583 44592234428706874524020375)
          ·
            refine ⟨66888351643060311786030563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44592234428706874524020375 66888351643060311786030563)
            ·
              refine ⟨100332527464590467679045845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66888351643060311786030563 100332527464590467679045845)
              ·
                refine ⟨2351543612451339086227637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100332527464590467679045845 2351543612451339086227637)
                ·
                  refine ⟨220457213667313039333841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2351543612451339086227637 220457213667313039333841)
                  ·
                    rfl

theorem cell22_1932025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_1932025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932025 prefixEnd_1932025 := by exact prefixLift 1932025
  have htrace : WordTrace (prefixWord ++ tailWord_1932025) baseStart_1932025 baseEnd_1932025 := by
    simpa [prefixWord, tailWord_1932025, baseEnd_1932025] using wordTrace_append hprefix tailTrace_1932025
  have hstable : (prefixWord ++ tailWord_1932025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932025).length < 2 ^ (prefixWord ++ tailWord_1932025).sum := by decide
  have hdescent : baseEnd_1932025 < baseStart_1932025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932072 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1932072 : Nat := 118140960795 + 1932072 * 2 ^ 59
def prefixEnd_1932072 : Nat := 4983230072969 + 3 ^ 40 * 1932072 * 2
def baseEnd_1932072 : Nat := 661387730062446662076379

theorem tailTrace_1932072 : CollatzResearch.WordTrace tailWord_1932072 prefixEnd_1932072 661387730062446662076379 := by
  unfold tailWord_1932072
  simp only [CollatzResearch.WordTrace]
  refine ⟨35234227528220295236163235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46978970037627060314884313 35234227528220295236163235)
  ·
    refine ⟨52851341292330442854244853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35234227528220295236163235 52851341292330442854244853)
    ·
      refine ⟨4954813246155979017585455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52851341292330442854244853 4954813246155979017585455)
      ·
        refine ⟨7432219869233968526378183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4954813246155979017585455 7432219869233968526378183)
        ·
          refine ⟨11148329803850952789567275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7432219869233968526378183 11148329803850952789567275)
          ·
            refine ⟨16722494705776429184350913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11148329803850952789567275 16722494705776429184350913)
            ·
              refine ⟨12541871029332321888263185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16722494705776429184350913 12541871029332321888263185)
              ·
                refine ⟨9406403271999241416197389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12541871029332321888263185 9406403271999241416197389)
                ·
                  refine ⟨3527401226999715531074021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9406403271999241416197389 3527401226999715531074021)
                  ·
                    refine ⟨661387730062446662076379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527401226999715531074021 661387730062446662076379)
                    ·
                      rfl

theorem cell22_1932072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1932072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932072 prefixEnd_1932072 := by exact prefixLift 1932072
  have htrace : WordTrace (prefixWord ++ tailWord_1932072) baseStart_1932072 baseEnd_1932072 := by
    simpa [prefixWord, tailWord_1932072, baseEnd_1932072] using wordTrace_append hprefix tailTrace_1932072
  have hstable : (prefixWord ++ tailWord_1932072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932072).length < 2 ^ (prefixWord ++ tailWord_1932072).sum := by decide
  have hdescent : baseEnd_1932072 < baseStart_1932072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932117 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1932117 : Nat := 118140960795 + 1932117 * 2 ^ 59
def prefixEnd_1932117 : Nat := 4983230072969 + 3 ^ 40 * 1932117 * 2
def baseEnd_1932117 : Nat := 661403134482081544701241

theorem tailTrace_1932117 : CollatzResearch.WordTrace tailWord_1932117 prefixEnd_1932117 661403134482081544701241 := by
  unfold tailWord_1932117
  simp only [CollatzResearch.WordTrace]
  refine ⟨70470096341277563157714605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980064227518375438476403 70470096341277563157714605)
  ·
    refine ⟨26426286127979086184142977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70470096341277563157714605 26426286127979086184142977)
    ·
      refine ⟨19819714595984314638107233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26426286127979086184142977 19819714595984314638107233)
      ·
        refine ⟨14864785946988235978580425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19819714595984314638107233 14864785946988235978580425)
        ·
          refine ⟨11148589460241176983935319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14864785946988235978580425 11148589460241176983935319)
          ·
            refine ⟨16722884190361765475902979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11148589460241176983935319 16722884190361765475902979)
            ·
              refine ⟨25084326285542648213854469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16722884190361765475902979 25084326285542648213854469)
              ·
                refine ⟨4703311178539246540097713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25084326285542648213854469 4703311178539246540097713)
                ·
                  refine ⟨3527483383904434905073285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703311178539246540097713 3527483383904434905073285)
                  ·
                    refine ⟨661403134482081544701241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527483383904434905073285 661403134482081544701241)
                    ·
                      rfl

theorem cell22_1932117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1932117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932117 prefixEnd_1932117 := by exact prefixLift 1932117
  have htrace : WordTrace (prefixWord ++ tailWord_1932117) baseStart_1932117 baseEnd_1932117 := by
    simpa [prefixWord, tailWord_1932117, baseEnd_1932117] using wordTrace_append hprefix tailTrace_1932117
  have hstable : (prefixWord ++ tailWord_1932117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932117).length < 2 ^ (prefixWord ++ tailWord_1932117).sum := by decide
  have hdescent : baseEnd_1932117 < baseStart_1932117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932119 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 2, 3]
def baseStart_1932119 : Nat := 118140960795 + 1932119 * 2 ^ 59
def prefixEnd_1932119 : Nat := 4983230072969 + 3 ^ 40 * 1932119 * 2
def baseEnd_1932119 : Nat := 661403819122954206151235

theorem tailTrace_1932119 : CollatzResearch.WordTrace tailWord_1932119 prefixEnd_1932119 661403819122954206151235 := by
  unfold tailWord_1932119
  simp only [CollatzResearch.WordTrace]
  refine ⟨70470169287270317499287411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980112858180211666191607 70470169287270317499287411)
  ·
    refine ⟨105705253930905476248931117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70470169287270317499287411 105705253930905476248931117)
    ·
      refine ⟨39639470224089553593349169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105705253930905476248931117 39639470224089553593349169)
      ·
        refine ⟨29729602668067165195011877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39639470224089553593349169 29729602668067165195011877)
        ·
          refine ⟨5574300500262593474064727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29729602668067165195011877 5574300500262593474064727)
          ·
            refine ⟨8361450750393890211097091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574300500262593474064727 8361450750393890211097091)
            ·
              refine ⟨12542176125590835316645637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8361450750393890211097091 12542176125590835316645637)
              ·
                refine ⟨2351658023548281621871057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12542176125590835316645637 2351658023548281621871057)
                ·
                  refine ⟨1763743517661211216403293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351658023548281621871057 1763743517661211216403293)
                  ·
                    refine ⟨661403819122954206151235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763743517661211216403293 661403819122954206151235)
                    ·
                      rfl

theorem cell22_1932119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_1932119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932119 prefixEnd_1932119 := by exact prefixLift 1932119
  have htrace : WordTrace (prefixWord ++ tailWord_1932119) baseStart_1932119 baseEnd_1932119 := by
    simpa [prefixWord, tailWord_1932119, baseEnd_1932119] using wordTrace_append hprefix tailTrace_1932119
  have hstable : (prefixWord ++ tailWord_1932119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932119).length < 2 ^ (prefixWord ++ tailWord_1932119).sum := by decide
  have hdescent : baseEnd_1932119 < baseStart_1932119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932121 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 4]
def baseStart_1932121 : Nat := 118140960795 + 1932121 * 2 ^ 59
def prefixEnd_1932121 : Nat := 4983230072969 + 3 ^ 40 * 1932121 * 2
def baseEnd_1932121 : Nat := 220468167921275622533743

theorem tailTrace_1932121 : CollatzResearch.WordTrace tailWord_1932121 prefixEnd_1932121 220468167921275622533743 := by
  unfold tailWord_1932121
  simp only [CollatzResearch.WordTrace]
  refine ⟨70470242233263071840860217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980161488842047893906811 70470242233263071840860217)
  ·
    refine ⟨52852681674947303880645163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70470242233263071840860217 52852681674947303880645163)
    ·
      refine ⟨79279022512420955820967745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52852681674947303880645163 79279022512420955820967745)
      ·
        refine ⟨59459266884315716865725809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79279022512420955820967745 59459266884315716865725809)
        ·
          refine ⟨44594450163236787649294357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59459266884315716865725809 44594450163236787649294357)
          ·
            refine ⟨2090364851401724421060673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44594450163236787649294357 2090364851401724421060673)
            ·
              refine ⟨1567773638551293315795505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090364851401724421060673 1567773638551293315795505)
              ·
                refine ⟨1175830228913469986846629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567773638551293315795505 1175830228913469986846629)
                ·
                  refine ⟨220468167921275622533743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1175830228913469986846629 220468167921275622533743)
                  ·
                    rfl

theorem cell22_1932121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_1932121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932121 prefixEnd_1932121 := by exact prefixLift 1932121
  have htrace : WordTrace (prefixWord ++ tailWord_1932121) baseStart_1932121 baseEnd_1932121 := by
    simpa [prefixWord, tailWord_1932121, baseEnd_1932121] using wordTrace_append hprefix tailTrace_1932121
  have hstable : (prefixWord ++ tailWord_1932121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932121).length < 2 ^ (prefixWord ++ tailWord_1932121).sum := by decide
  have hdescent : baseEnd_1932121 < baseStart_1932121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932132 : List Nat := [2, 3, 1, 1, 4, 1, 3, 7]
def baseStart_1932132 : Nat := 118140960795 + 1932132 * 2 ^ 59
def prefixEnd_1932132 : Nat := 4983230072969 + 3 ^ 40 * 1932132 * 2
def baseEnd_1932132 : Nat := 73489807698736278397355

theorem tailTrace_1932132 : CollatzResearch.WordTrace tailWord_1932132 prefixEnd_1932132 73489807698736278397355 := by
  unfold tailWord_1932132
  simp only [CollatzResearch.WordTrace]
  refine ⟨35235321718111610359755325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46980428957482147146340433 35235321718111610359755325)
  ·
    refine ⟨13213245644291853884908247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35235321718111610359755325 13213245644291853884908247)
    ·
      refine ⟨19819868466437780827362371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13213245644291853884908247 19819868466437780827362371)
      ·
        refine ⟨29729802699656671241043557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19819868466437780827362371 29729802699656671241043557)
        ·
          refine ⟨5574338006185625857695667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29729802699656671241043557 5574338006185625857695667)
          ·
            refine ⟨8361507009278438786543501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574338006185625857695667 8361507009278438786543501)
            ·
              refine ⟨3135565128479414544953813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8361507009278438786543501 3135565128479414544953813)
              ·
                refine ⟨73489807698736278397355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3135565128479414544953813 73489807698736278397355)
                ·
                  rfl

theorem cell22_1932132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_1932132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932132 prefixEnd_1932132 := by exact prefixLift 1932132
  have htrace : WordTrace (prefixWord ++ tailWord_1932132) baseStart_1932132 baseEnd_1932132 := by
    simpa [prefixWord, tailWord_1932132, baseEnd_1932132] using wordTrace_append hprefix tailTrace_1932132
  have hstable : (prefixWord ++ tailWord_1932132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932132).length < 2 ^ (prefixWord ++ tailWord_1932132).sum := by decide
  have hdescent : baseEnd_1932132 < baseStart_1932132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932147 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 5, 3]
def baseStart_1932147 : Nat := 118140960795 + 1932147 * 2 ^ 59
def prefixEnd_1932147 : Nat := 4983230072969 + 3 ^ 40 * 1932147 * 2
def baseEnd_1932147 : Nat := 661413404095171466451149

theorem tailTrace_1932147 : CollatzResearch.WordTrace tailWord_1932147 prefixEnd_1932147 661413404095171466451149 := by
  unfold tailWord_1932147
  simp only [CollatzResearch.WordTrace]
  refine ⟨70471190531168878281306695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980793687445918854204463 70471190531168878281306695)
  ·
    refine ⟨105706785796753317421960043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70471190531168878281306695 105706785796753317421960043)
    ·
      refine ⟨158560178695129976132940065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105706785796753317421960043 158560178695129976132940065)
      ·
        refine ⟨118920134021347482099705049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158560178695129976132940065 118920134021347482099705049)
        ·
          refine ⟨89190100516010611574778787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118920134021347482099705049 89190100516010611574778787)
          ·
            refine ⟨133785150774015917362168181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89190100516010611574778787 133785150774015917362168181)
            ·
              refine ⟨12542357885063992252703267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133785150774015917362168181 12542357885063992252703267)
              ·
                refine ⟨18813536827595988379054901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12542357885063992252703267 18813536827595988379054901)
                ·
                  refine ⟨1763769077587123910536397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18813536827595988379054901 1763769077587123910536397)
                  ·
                    refine ⟨661413404095171466451149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763769077587123910536397 661413404095171466451149)
                    ·
                      rfl

theorem cell22_1932147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 3].length) (baseStart_1932147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932147 prefixEnd_1932147 := by exact prefixLift 1932147
  have htrace : WordTrace (prefixWord ++ tailWord_1932147) baseStart_1932147 baseEnd_1932147 := by
    simpa [prefixWord, tailWord_1932147, baseEnd_1932147] using wordTrace_append hprefix tailTrace_1932147
  have hstable : (prefixWord ++ tailWord_1932147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932147).length < 2 ^ (prefixWord ++ tailWord_1932147).sum := by decide
  have hdescent : baseEnd_1932147 < baseStart_1932147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932149 : List Nat := [1, 3, 4, 1, 1, 3, 3, 6]
def baseStart_1932149 : Nat := 118140960795 + 1932149 * 2 ^ 59
def prefixEnd_1932149 : Nat := 4983230072969 + 3 ^ 40 * 1932149 * 2
def baseEnd_1932149 : Nat := 73490454304004903100127

theorem tailTrace_1932149 : CollatzResearch.WordTrace tailWord_1932149 prefixEnd_1932149 73490454304004903100127 := by
  unfold tailWord_1932149
  simp only [CollatzResearch.WordTrace]
  refine ⟨70471263477161632622879501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980842318107755081919667 70471263477161632622879501)
  ·
    refine ⟨26426723803935612233579813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70471263477161632622879501 26426723803935612233579813)
    ·
      refine ⟨4955010713237927293796215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26426723803935612233579813 4955010713237927293796215)
      ·
        refine ⟨7432516069856890940694323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955010713237927293796215 7432516069856890940694323)
        ·
          refine ⟨11148774104785336411041485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7432516069856890940694323 11148774104785336411041485)
          ·
            refine ⟨4180790289294501154140557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11148774104785336411041485 4180790289294501154140557)
            ·
              refine ⟨1567796358485437932802709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4180790289294501154140557 1567796358485437932802709)
              ·
                refine ⟨73490454304004903100127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1567796358485437932802709 73490454304004903100127)
                ·
                  rfl

theorem cell22_1932149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 6].length) (baseStart_1932149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932149 prefixEnd_1932149 := by exact prefixLift 1932149
  have htrace : WordTrace (prefixWord ++ tailWord_1932149) baseStart_1932149 baseEnd_1932149 := by
    simpa [prefixWord, tailWord_1932149, baseEnd_1932149] using wordTrace_append hprefix tailTrace_1932149
  have hstable : (prefixWord ++ tailWord_1932149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932149).length < 2 ^ (prefixWord ++ tailWord_1932149).sum := by decide
  have hdescent : baseEnd_1932149 < baseStart_1932149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932175 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_1932175 : Nat := 118140960795 + 1932175 * 2 ^ 59
def prefixEnd_1932175 : Nat := 4983230072969 + 3 ^ 40 * 1932175 * 2
def baseEnd_1932175 : Nat := 661422989067388726751063

theorem tailTrace_1932175 : CollatzResearch.WordTrace tailWord_1932175 prefixEnd_1932175 661422989067388726751063 := by
  unfold tailWord_1932175
  simp only [CollatzResearch.WordTrace]
  refine ⟨70472211775067439063325979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46981474516711626042217319 70472211775067439063325979)
  ·
    refine ⟨105708317662601158594988969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70472211775067439063325979 105708317662601158594988969)
    ·
      refine ⟨79281238246950868946241727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105708317662601158594988969 79281238246950868946241727)
      ·
        refine ⟨118921857370426303419362591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79281238246950868946241727 118921857370426303419362591)
        ·
          refine ⟨178382786055639455129043887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118921857370426303419362591 178382786055639455129043887)
          ·
            refine ⟨267574179083459182693565831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178382786055639455129043887 267574179083459182693565831)
            ·
              refine ⟨401361268625188774040348747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267574179083459182693565831 401361268625188774040348747)
              ·
                refine ⟨602041902937783161060523121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401361268625188774040348747 602041902937783161060523121)
                ·
                  refine ⟨451531427203337370795392341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602041902937783161060523121 451531427203337370795392341)
                  ·
                    refine ⟨661422989067388726751063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 451531427203337370795392341 661422989067388726751063)
                    ·
                      rfl

theorem cell22_1932175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_1932175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932175 prefixEnd_1932175 := by exact prefixLift 1932175
  have htrace : WordTrace (prefixWord ++ tailWord_1932175) baseStart_1932175 baseEnd_1932175 := by
    simpa [prefixWord, tailWord_1932175, baseEnd_1932175] using wordTrace_append hprefix tailTrace_1932175
  have hstable : (prefixWord ++ tailWord_1932175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932175).length < 2 ^ (prefixWord ++ tailWord_1932175).sum := by decide
  have hdescent : baseEnd_1932175 < baseStart_1932175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932181 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_1932181 : Nat := 118140960795 + 1932181 * 2 ^ 59
def prefixEnd_1932181 : Nat := 4983230072969 + 3 ^ 40 * 1932181 * 2
def baseEnd_1932181 : Nat := 661425042990006711101045

theorem tailTrace_1932181 : CollatzResearch.WordTrace tailWord_1932181 prefixEnd_1932181 661425042990006711101045 := by
  unfold tailWord_1932181
  simp only [CollatzResearch.WordTrace]
  refine ⟨70472430613045702088044397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46981620408697134725362931 70472430613045702088044397)
  ·
    refine ⟨26427161479892138283016649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70472430613045702088044397 26427161479892138283016649)
    ·
      refine ⟨19820371109919103712262487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26427161479892138283016649 19820371109919103712262487)
      ·
        refine ⟨29730556664878655568393731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19820371109919103712262487 29730556664878655568393731)
        ·
          refine ⟨44595834997317983352590597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29730556664878655568393731 44595834997317983352590597)
          ·
            refine ⟨8361719061997121878610737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44595834997317983352590597 8361719061997121878610737)
            ·
              refine ⟨6271289296497841408958053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8361719061997121878610737 6271289296497841408958053)
              ·
                refine ⟨1175866743093345264179635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6271289296497841408958053 1175866743093345264179635)
                ·
                  refine ⟨1763800114640017896269453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175866743093345264179635 1763800114640017896269453)
                  ·
                    refine ⟨661425042990006711101045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763800114640017896269453 661425042990006711101045)
                    ·
                      rfl

theorem cell22_1932181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_1932181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932181 prefixEnd_1932181 := by exact prefixLift 1932181
  have htrace : WordTrace (prefixWord ++ tailWord_1932181) baseStart_1932181 baseEnd_1932181 := by
    simpa [prefixWord, tailWord_1932181, baseEnd_1932181] using wordTrace_append hprefix tailTrace_1932181
  have hstable : (prefixWord ++ tailWord_1932181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932181).length < 2 ^ (prefixWord ++ tailWord_1932181).sum := by decide
  have hdescent : baseEnd_1932181 < baseStart_1932181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932192 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_1932192 : Nat := 118140960795 + 1932192 * 2 ^ 59
def prefixEnd_1932192 : Nat := 4983230072969 + 3 ^ 40 * 1932192 * 2
def baseEnd_1932192 : Nat := 661428808514806349076011

theorem tailTrace_1932192 : CollatzResearch.WordTrace tailWord_1932192 prefixEnd_1932192 661428808514806349076011 := by
  unfold tailWord_1932192
  simp only [CollatzResearch.WordTrace]
  refine ⟨35236415908002925483347415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46981887877337233977796553 35236415908002925483347415)
  ·
    refine ⟨52854623862004388225021123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35236415908002925483347415 52854623862004388225021123)
    ·
      refine ⟨79281935793006582337531685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52854623862004388225021123 79281935793006582337531685)
      ·
        refine ⟨14865362961188734188287191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79281935793006582337531685 14865362961188734188287191)
        ·
          refine ⟨22298044441783101282430787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14865362961188734188287191 22298044441783101282430787)
          ·
            refine ⟨33447066662674651923646181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22298044441783101282430787 33447066662674651923646181)
            ·
              refine ⟨6271324999251497235683659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33447066662674651923646181 6271324999251497235683659)
              ·
                refine ⟨9406987498877245853525489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271324999251497235683659 9406987498877245853525489)
                ·
                  refine ⟨7055240624157934390144117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9406987498877245853525489 7055240624157934390144117)
                  ·
                    refine ⟨661428808514806349076011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7055240624157934390144117 661428808514806349076011)
                    ·
                      rfl

theorem cell22_1932192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_1932192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932192 prefixEnd_1932192 := by exact prefixLift 1932192
  have htrace : WordTrace (prefixWord ++ tailWord_1932192) baseStart_1932192 baseEnd_1932192 := by
    simpa [prefixWord, tailWord_1932192, baseEnd_1932192] using wordTrace_append hprefix tailTrace_1932192
  have hstable : (prefixWord ++ tailWord_1932192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932192).length < 2 ^ (prefixWord ++ tailWord_1932192).sum := by decide
  have hdescent : baseEnd_1932192 < baseStart_1932192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932224 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_1932224 : Nat := 118140960795 + 1932224 * 2 ^ 59
def prefixEnd_1932224 : Nat := 4983230072969 + 3 ^ 40 * 1932224 * 2
def baseEnd_1932224 : Nat := 661439762768768932275913

theorem tailTrace_1932224 : CollatzResearch.WordTrace tailWord_1932224 prefixEnd_1932224 661439762768768932275913 := by
  unfold tailWord_1932224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35236999475944960215929863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46982665967926613621239817 35236999475944960215929863)
  ·
    refine ⟨52855499213917440323894795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35236999475944960215929863 52855499213917440323894795)
    ·
      refine ⟨79283248820876160485842193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52855499213917440323894795 79283248820876160485842193)
      ·
        refine ⟨59462436615657120364381645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79283248820876160485842193 59462436615657120364381645)
        ·
          refine ⟨22298413730871420136643117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59462436615657120364381645 22298413730871420136643117)
          ·
            refine ⟨8361905149076782551241169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22298413730871420136643117 8361905149076782551241169)
            ·
              refine ⟨6271428861807586913430877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8361905149076782551241169 6271428861807586913430877)
              ·
                refine ⟨2351785823177845092536579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6271428861807586913430877 2351785823177845092536579)
                ·
                  refine ⟨3527678734766767638804869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351785823177845092536579 3527678734766767638804869)
                  ·
                    refine ⟨661439762768768932275913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527678734766767638804869 661439762768768932275913)
                    ·
                      rfl

theorem cell22_1932224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_1932224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932224 prefixEnd_1932224 := by exact prefixLift 1932224
  have htrace : WordTrace (prefixWord ++ tailWord_1932224) baseStart_1932224 baseEnd_1932224 := by
    simpa [prefixWord, tailWord_1932224, baseEnd_1932224] using wordTrace_append hprefix tailTrace_1932224
  have hstable : (prefixWord ++ tailWord_1932224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932224).length < 2 ^ (prefixWord ++ tailWord_1932224).sum := by decide
  have hdescent : baseEnd_1932224 < baseStart_1932224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932239 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 6]
def baseStart_1932239 : Nat := 118140960795 + 1932239 * 2 ^ 59
def prefixEnd_1932239 : Nat := 4983230072969 + 3 ^ 40 * 1932239 * 2
def baseEnd_1932239 : Nat := 220481632525104631050289

theorem tailTrace_1932239 : CollatzResearch.WordTrace tailWord_1932239 prefixEnd_1932239 220481632525104631050289 := by
  unfold tailWord_1932239
  simp only [CollatzResearch.WordTrace]
  refine ⟨70474546046835577993655771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46983030697890385329103847 70474546046835577993655771)
  ·
    refine ⟨105711819070253366990483657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70474546046835577993655771 105711819070253366990483657)
    ·
      refine ⟨79283864302690025242862743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105711819070253366990483657 79283864302690025242862743)
      ·
        refine ⟨118925796454035037864294115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79283864302690025242862743 118925796454035037864294115)
        ·
          refine ⟨178388694681052556796441173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118925796454035037864294115 178388694681052556796441173)
          ·
            refine ⟨2090492515793584649958295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 178388694681052556796441173 2090492515793584649958295)
            ·
              refine ⟨3135738773690376974937443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090492515793584649958295 3135738773690376974937443)
              ·
                refine ⟨4703608160535565462406165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135738773690376974937443 4703608160535565462406165)
                ·
                  refine ⟨220481632525104631050289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4703608160535565462406165 220481632525104631050289)
                  ·
                    rfl

theorem cell22_1932239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 6].length) (baseStart_1932239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932239 prefixEnd_1932239 := by exact prefixLift 1932239
  have htrace : WordTrace (prefixWord ++ tailWord_1932239) baseStart_1932239 baseEnd_1932239 := by
    simpa [prefixWord, tailWord_1932239, baseEnd_1932239] using wordTrace_append hprefix tailTrace_1932239
  have hstable : (prefixWord ++ tailWord_1932239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932239).length < 2 ^ (prefixWord ++ tailWord_1932239).sum := by decide
  have hdescent : baseEnd_1932239 < baseStart_1932239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932258 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1932258 : Nat := 118140960795 + 1932258 * 2 ^ 59
def prefixEnd_1932258 : Nat := 4983230072969 + 3 ^ 40 * 1932258 * 2
def baseEnd_1932258 : Nat := 661451401663604176925809

theorem tailTrace_1932258 : CollatzResearch.WordTrace tailWord_1932258 prefixEnd_1932258 661451401663604176925809 := by
  unfold tailWord_1932258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618809758441686059649357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46983492689177829492398285 17618809758441686059649357)
  ·
    refine ⟨6607053659415632272368509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17618809758441686059649357 6607053659415632272368509)
    ·
      refine ⟨2477645122280862102138191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6607053659415632272368509 2477645122280862102138191)
      ·
        refine ⟨3716467683421293153207287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2477645122280862102138191 3716467683421293153207287)
        ·
          refine ⟨5574701525131939729810931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716467683421293153207287 5574701525131939729810931)
          ·
            refine ⟨8362052287697909594716397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574701525131939729810931 8362052287697909594716397)
            ·
              refine ⟨3135769607886716098018649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8362052287697909594716397 3135769607886716098018649)
              ·
                refine ⟨2351827205915037073513987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135769607886716098018649 2351827205915037073513987)
                ·
                  refine ⟨3527740808872555610270981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351827205915037073513987 3527740808872555610270981)
                  ·
                    refine ⟨661451401663604176925809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527740808872555610270981 661451401663604176925809)
                    ·
                      rfl

theorem cell22_1932258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1932258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932258 prefixEnd_1932258 := by exact prefixLift 1932258
  have htrace : WordTrace (prefixWord ++ tailWord_1932258) baseStart_1932258 baseEnd_1932258 := by
    simpa [prefixWord, tailWord_1932258, baseEnd_1932258] using wordTrace_append hprefix tailTrace_1932258
  have hstable : (prefixWord ++ tailWord_1932258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932258).length < 2 ^ (prefixWord ++ tailWord_1932258).sum := by decide
  have hdescent : baseEnd_1932258 < baseStart_1932258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932290 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1932290 : Nat := 118140960795 + 1932290 * 2 ^ 59
def prefixEnd_1932290 : Nat := 4983230072969 + 3 ^ 40 * 1932290 * 2
def baseEnd_1932290 : Nat := 220487451972522253375237

theorem tailTrace_1932290 : CollatzResearch.WordTrace tailWord_1932290 prefixEnd_1932290 220487451972522253375237 := by
  unfold tailWord_1932290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619101542412703425940581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46984270779767209135841549 17619101542412703425940581)
  ·
    refine ⟨3303581539202381892363859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17619101542412703425940581 3303581539202381892363859)
    ·
      refine ⟨4955372308803572838545789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303581539202381892363859 4955372308803572838545789)
      ·
        refine ⟨1858264615801339814454671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4955372308803572838545789 1858264615801339814454671)
        ·
          refine ⟨2787396923702009721682007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858264615801339814454671 2787396923702009721682007)
          ·
            refine ⟨4181095385553014582523011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787396923702009721682007 4181095385553014582523011)
            ·
              refine ⟨6271643078329521873784517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181095385553014582523011 6271643078329521873784517)
              ·
                refine ⟨1175933077186785351334597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6271643078329521873784517 1175933077186785351334597)
                ·
                  refine ⟨220487451972522253375237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1175933077186785351334597 220487451972522253375237)
                  ·
                    rfl

theorem cell22_1932290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1932290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932290 prefixEnd_1932290 := by exact prefixLift 1932290
  have htrace : WordTrace (prefixWord ++ tailWord_1932290) baseStart_1932290 baseEnd_1932290 := by
    simpa [prefixWord, tailWord_1932290, baseEnd_1932290] using wordTrace_append hprefix tailTrace_1932290
  have hstable : (prefixWord ++ tailWord_1932290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932290).length < 2 ^ (prefixWord ++ tailWord_1932290).sum := by decide
  have hdescent : baseEnd_1932290 < baseStart_1932290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932320 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 2, 4]
def baseStart_1932320 : Nat := 118140960795 + 1932320 * 2 ^ 59
def prefixEnd_1932320 : Nat := 4983230072969 + 3 ^ 40 * 1932320 * 2
def baseEnd_1932320 : Nat := 661472625530656681875619

theorem tailTrace_1932320 : CollatzResearch.WordTrace tailWord_1932320 prefixEnd_1932320 661472625530656681875619 := by
  unfold tailWord_1932320
  simp only [CollatzResearch.WordTrace]
  refine ⟨35238750179771064413677207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46985000239694752551569609 35238750179771064413677207)
  ·
    refine ⟨52858125269656596620515811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35238750179771064413677207 52858125269656596620515811)
    ·
      refine ⟨79287187904484894930773717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52858125269656596620515811 79287187904484894930773717)
      ·
        refine ⟨1858293466511364724940009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79287187904484894930773717 1858293466511364724940009)
        ·
          refine ⟨1393720099883523543705007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1858293466511364724940009 1393720099883523543705007)
          ·
            refine ⟨2090580149825285315557511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393720099883523543705007 2090580149825285315557511)
            ·
              refine ⟨3135870224737927973336267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090580149825285315557511 3135870224737927973336267)
              ·
                refine ⟨4703805337106891960004401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135870224737927973336267 4703805337106891960004401)
                ·
                  refine ⟨3527854002830168970003301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703805337106891960004401 3527854002830168970003301)
                  ·
                    refine ⟨661472625530656681875619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527854002830168970003301 661472625530656681875619)
                    ·
                      rfl

theorem cell22_1932320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_1932320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932320 prefixEnd_1932320 := by exact prefixLift 1932320
  have htrace : WordTrace (prefixWord ++ tailWord_1932320) baseStart_1932320 baseEnd_1932320 := by
    simpa [prefixWord, tailWord_1932320, baseEnd_1932320] using wordTrace_append hprefix tailTrace_1932320
  have hstable : (prefixWord ++ tailWord_1932320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932320).length < 2 ^ (prefixWord ++ tailWord_1932320).sum := by decide
  have hdescent : baseEnd_1932320 < baseStart_1932320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932344 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_1932344 : Nat := 118140960795 + 1932344 * 2 ^ 59
def prefixEnd_1932344 : Nat := 4983230072969 + 3 ^ 40 * 1932344 * 2
def baseEnd_1932344 : Nat := 661480841221128619275545

theorem tailTrace_1932344 : CollatzResearch.WordTrace tailWord_1932344 prefixEnd_1932344 661480841221128619275545 := by
  unfold tailWord_1932344
  simp only [CollatzResearch.WordTrace]
  refine ⟨35239187855727590463114043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46985583807636787284152057 35239187855727590463114043)
  ·
    refine ⟨52858781783591385694671065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35239187855727590463114043 52858781783591385694671065)
    ·
      refine ⟨39644086337693539271003299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52858781783591385694671065 39644086337693539271003299)
      ·
        refine ⟨59466129506540308906504949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39644086337693539271003299 59466129506540308906504949)
        ·
          refine ⟨5574949641238153959984839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59466129506540308906504949 5574949641238153959984839)
          ·
            refine ⟨8362424461857230939977259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574949641238153959984839 8362424461857230939977259)
            ·
              refine ⟨12543636692785846409965889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362424461857230939977259 12543636692785846409965889)
              ·
                refine ⟨9407727519589384807474417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12543636692785846409965889 9407727519589384807474417)
                ·
                  refine ⟨7055795639692038605605813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9407727519589384807474417 7055795639692038605605813)
                  ·
                    refine ⟨661480841221128619275545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7055795639692038605605813 661480841221128619275545)
                    ·
                      rfl

theorem cell22_1932344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_1932344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932344 prefixEnd_1932344 := by exact prefixLift 1932344
  have htrace : WordTrace (prefixWord ++ tailWord_1932344) baseStart_1932344 baseEnd_1932344 := by
    simpa [prefixWord, tailWord_1932344, baseEnd_1932344] using wordTrace_append hprefix tailTrace_1932344
  have hstable : (prefixWord ++ tailWord_1932344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932344).length < 2 ^ (prefixWord ++ tailWord_1932344).sum := by decide
  have hdescent : baseEnd_1932344 < baseStart_1932344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932350 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1932350 : Nat := 118140960795 + 1932350 * 2 ^ 59
def prefixEnd_1932350 : Nat := 4983230072969 + 3 ^ 40 * 1932350 * 2
def baseEnd_1932350 : Nat := 661482895143746603625527

theorem tailTrace_1932350 : CollatzResearch.WordTrace tailWord_1932350 prefixEnd_1932350 661482895143746603625527 := by
  unfold tailWord_1932350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809824318679180493868313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46985729699622295967297669 8809824318679180493868313)
  ·
    refine ⟨6607368239009385370401235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8809824318679180493868313 6607368239009385370401235)
    ·
      refine ⟨9911052358514078055601853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607368239009385370401235 9911052358514078055601853)
      ·
        refine ⟨3716644634442779270850695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9911052358514078055601853 3716644634442779270850695)
        ·
          refine ⟨5574966951664168906276043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716644634442779270850695 5574966951664168906276043)
          ·
            refine ⟨8362450427496253359414065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574966951664168906276043 8362450427496253359414065)
            ·
              refine ⟨6271837820622190019560549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8362450427496253359414065 6271837820622190019560549)
              ·
                refine ⟨1175969591366660628667603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6271837820622190019560549 1175969591366660628667603)
                ·
                  refine ⟨1763954387049990943001405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175969591366660628667603 1763954387049990943001405)
                  ·
                    refine ⟨661482895143746603625527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763954387049990943001405 661482895143746603625527)
                    ·
                      rfl

theorem cell22_1932350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1932350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932350 prefixEnd_1932350 := by exact prefixLift 1932350
  have htrace : WordTrace (prefixWord ++ tailWord_1932350) baseStart_1932350 baseEnd_1932350 := by
    simpa [prefixWord, tailWord_1932350, baseEnd_1932350] using wordTrace_append hprefix tailTrace_1932350
  have hstable : (prefixWord ++ tailWord_1932350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932350).length < 2 ^ (prefixWord ++ tailWord_1932350).sum := by decide
  have hdescent : baseEnd_1932350 < baseStart_1932350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932376 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_1932376 : Nat := 118140960795 + 1932376 * 2 ^ 59
def prefixEnd_1932376 : Nat := 4983230072969 + 3 ^ 40 * 1932376 * 2
def baseEnd_1932376 : Nat := 661491795475091202475447

theorem tailTrace_1932376 : CollatzResearch.WordTrace tailWord_1932376 prefixEnd_1932376 661491795475091202475447 := by
  unfold tailWord_1932376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35239771423669625195696491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46986361898226166927595321 35239771423669625195696491)
  ·
    refine ⟨52859657135504437793544737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35239771423669625195696491 52859657135504437793544737)
    ·
      refine ⟨39644742851628328345158553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52859657135504437793544737 39644742851628328345158553)
      ·
        refine ⟨29733557138721246258868915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39644742851628328345158553 29733557138721246258868915)
        ·
          refine ⟨44600335708081869388303373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29733557138721246258868915 44600335708081869388303373)
          ·
            refine ⟨16725125890530701020613765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44600335708081869388303373 16725125890530701020613765)
            ·
              refine ⟨3135961104474506441365081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16725125890530701020613765 3135961104474506441365081)
              ·
                refine ⟨2351970828355879831023811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135961104474506441365081 2351970828355879831023811)
                ·
                  refine ⟨3527956242533819746535717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351970828355879831023811 3527956242533819746535717)
                  ·
                    refine ⟨661491795475091202475447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527956242533819746535717 661491795475091202475447)
                    ·
                      rfl

theorem cell22_1932376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_1932376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932376 prefixEnd_1932376 := by exact prefixLift 1932376
  have htrace : WordTrace (prefixWord ++ tailWord_1932376) baseStart_1932376 baseEnd_1932376 := by
    simpa [prefixWord, tailWord_1932376, baseEnd_1932376] using wordTrace_append hprefix tailTrace_1932376
  have hstable : (prefixWord ++ tailWord_1932376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932376).length < 2 ^ (prefixWord ++ tailWord_1932376).sum := by decide
  have hdescent : baseEnd_1932376 < baseStart_1932376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932389 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1932389 : Nat := 118140960795 + 1932389 * 2 ^ 59
def prefixEnd_1932389 : Nat := 4983230072969 + 3 ^ 40 * 1932389 * 2
def baseEnd_1932389 : Nat := 661496245640763501900407

theorem tailTrace_1932389 : CollatzResearch.WordTrace tailWord_1932389 prefixEnd_1932389 661496245640763501900407 := by
  unfold tailWord_1932389
  simp only [CollatzResearch.WordTrace]
  refine ⟨70480016996292153611616221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46986677997528102407744147 70480016996292153611616221)
  ·
    refine ⟨26430006373609557604356083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70480016996292153611616221 26430006373609557604356083)
    ·
      refine ⟨39645009560414336406534125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26430006373609557604356083 39645009560414336406534125)
      ·
        refine ⟨14866878585155376152450297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39645009560414336406534125 14866878585155376152450297)
        ·
          refine ⟨11150158938866532114337723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14866878585155376152450297 11150158938866532114337723)
          ·
            refine ⟨16725238408299798171506585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11150158938866532114337723 16725238408299798171506585)
            ·
              refine ⟨12543928806224848628629939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16725238408299798171506585 12543928806224848628629939)
              ·
                refine ⟨18815893209337272942944909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12543928806224848628629939 18815893209337272942944909)
                ·
                  refine ⟨7055959953501477353604341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18815893209337272942944909 7055959953501477353604341)
                  ·
                    refine ⟨661496245640763501900407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7055959953501477353604341 661496245640763501900407)
                    ·
                      rfl

theorem cell22_1932389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1932389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932389 prefixEnd_1932389 := by exact prefixLift 1932389
  have htrace : WordTrace (prefixWord ++ tailWord_1932389) baseStart_1932389 baseEnd_1932389 := by
    simpa [prefixWord, tailWord_1932389, baseEnd_1932389] using wordTrace_append hprefix tailTrace_1932389
  have hstable : (prefixWord ++ tailWord_1932389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932389).length < 2 ^ (prefixWord ++ tailWord_1932389).sum := by decide
  have hdescent : baseEnd_1932389 < baseStart_1932389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932414 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1932414 : Nat := 118140960795 + 1932414 * 2 ^ 59
def prefixEnd_1932414 : Nat := 4983230072969 + 3 ^ 40 * 1932414 * 2
def baseEnd_1932414 : Nat := 220501601217223923341777

theorem tailTrace_1932414 : CollatzResearch.WordTrace tailWord_1932414 prefixEnd_1932414 220501601217223923341777 := by
  unfold tailWord_1932414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810116102650197860159537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46987285880801055254184197 8810116102650197860159537)
  ·
    refine ⟨6607587076987648395119653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8810116102650197860159537 6607587076987648395119653)
    ·
      refine ⟨1238922576935184074084935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6607587076987648395119653 1238922576935184074084935)
      ·
        refine ⟨1858383865402776111127403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238922576935184074084935 1858383865402776111127403)
        ·
          refine ⟨2787575798104164166691105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858383865402776111127403 2787575798104164166691105)
          ·
            refine ⟨2090681848578123125018329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2787575798104164166691105 2090681848578123125018329)
            ·
              refine ⟨1568011386433592343763747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090681848578123125018329 1568011386433592343763747)
              ·
                refine ⟨2352017079650388515645621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568011386433592343763747 2352017079650388515645621)
                ·
                  refine ⟨220501601217223923341777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352017079650388515645621 220501601217223923341777)
                  ·
                    rfl

theorem cell22_1932414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1932414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932414 prefixEnd_1932414 := by exact prefixLift 1932414
  have htrace : WordTrace (prefixWord ++ tailWord_1932414) baseStart_1932414 baseEnd_1932414 := by
    simpa [prefixWord, tailWord_1932414, baseEnd_1932414] using wordTrace_append hprefix tailTrace_1932414
  have hstable : (prefixWord ++ tailWord_1932414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932414).length < 2 ^ (prefixWord ++ tailWord_1932414).sum := by decide
  have hdescent : baseEnd_1932414 < baseStart_1932414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932419 : List Nat := [1, 1, 1, 3, 3, 2, 4, 7]
def baseStart_1932419 : Nat := 118140960795 + 1932419 * 2 ^ 59
def prefixEnd_1932419 : Nat := 4983230072969 + 3 ^ 40 * 1932419 * 2
def baseEnd_1932419 : Nat := 73500723917094824850035

theorem tailTrace_1932419 : CollatzResearch.WordTrace tailWord_1932419 prefixEnd_1932419 73500723917094824850035 := by
  unfold tailWord_1932419
  simp only [CollatzResearch.WordTrace]
  refine ⟨70481111186183468735208311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46987407457455645823472207 70481111186183468735208311)
  ·
    refine ⟨105721666779275203102812467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70481111186183468735208311 105721666779275203102812467)
    ·
      refine ⟨158582500168912804654218701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105721666779275203102812467 158582500168912804654218701)
      ·
        refine ⟨59468437563342301745332013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158582500168912804654218701 59468437563342301745332013)
        ·
          refine ⟨22300664086253363154499505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59468437563342301745332013 22300664086253363154499505)
          ·
            refine ⟨16725498064690022365874629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22300664086253363154499505 16725498064690022365874629)
            ·
              refine ⟨3136030887129379193601493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16725498064690022365874629 3136030887129379193601493)
              ·
                refine ⟨73500723917094824850035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3136030887129379193601493 73500723917094824850035)
                ·
                  rfl

theorem cell22_1932419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 7].length) (baseStart_1932419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932419 prefixEnd_1932419 := by exact prefixLift 1932419
  have htrace : WordTrace (prefixWord ++ tailWord_1932419) baseStart_1932419 baseEnd_1932419 := by
    simpa [prefixWord, tailWord_1932419, baseEnd_1932419] using wordTrace_append hprefix tailTrace_1932419
  have hstable : (prefixWord ++ tailWord_1932419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932419).length < 2 ^ (prefixWord ++ tailWord_1932419).sum := by decide
  have hdescent : baseEnd_1932419 < baseStart_1932419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932479 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_1932479 : Nat := 118140960795 + 1932479 * 2 ^ 59
def prefixEnd_1932479 : Nat := 4983230072969 + 3 ^ 40 * 1932479 * 2
def baseEnd_1932479 : Nat := 661527054480033267150131

theorem tailTrace_1932479 : CollatzResearch.WordTrace tailWord_1932479 prefixEnd_1932479 661527054480033267150131 := by
  unfold tailWord_1932479
  simp only [CollatzResearch.WordTrace]
  refine ⟨70483299565966098982392491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46988866377310732654928327 70483299565966098982392491)
  ·
    refine ⟨105724949348949148473588737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70483299565966098982392491 105724949348949148473588737)
    ·
      refine ⟨79293712011711861355191553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105724949348949148473588737 79293712011711861355191553)
      ·
        refine ⟨59470284008783896016393665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79293712011711861355191553 59470284008783896016393665)
        ·
          refine ⟨44602713006587922012295249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59470284008783896016393665 44602713006587922012295249)
          ·
            refine ⟨33452034754940941509221437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44602713006587922012295249 33452034754940941509221437)
            ·
              refine ⟨12544513033102853065958039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33452034754940941509221437 12544513033102853065958039)
              ·
                refine ⟨18816769549654279598937059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544513033102853065958039 18816769549654279598937059)
                ·
                  refine ⟨28225154324481419398405589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18816769549654279598937059 28225154324481419398405589)
                  ·
                    refine ⟨661527054480033267150131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28225154324481419398405589 661527054480033267150131)
                    ·
                      rfl

theorem cell22_1932479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_1932479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932479 prefixEnd_1932479 := by exact prefixLift 1932479
  have htrace : WordTrace (prefixWord ++ tailWord_1932479) baseStart_1932479 baseEnd_1932479 := by
    simpa [prefixWord, tailWord_1932479, baseEnd_1932479] using wordTrace_append hprefix tailTrace_1932479
  have hstable : (prefixWord ++ tailWord_1932479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932479).length < 2 ^ (prefixWord ++ tailWord_1932479).sum := by decide
  have hdescent : baseEnd_1932479 < baseStart_1932479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932526 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1932526 : Nat := 118140960795 + 1932526 * 2 ^ 59
def prefixEnd_1932526 : Nat := 4983230072969 + 3 ^ 40 * 1932526 * 2
def baseEnd_1932526 : Nat := 220514381180180270408329

theorem tailTrace_1932526 : CollatzResearch.WordTrace tailWord_1932526 prefixEnd_1932526 220514381180180270408329 := by
  unfold tailWord_1932526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810626724599478251169179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46990009197863884006235621 8810626724599478251169179)
  ·
    refine ⟨13215940086899217376753769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810626724599478251169179 13215940086899217376753769)
    ·
      refine ⟨9911955065174413032565327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13215940086899217376753769 9911955065174413032565327)
      ·
        refine ⟨14867932597761619548847991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9911955065174413032565327 14867932597761619548847991)
        ·
          refine ⟨22301898896642429323271987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14867932597761619548847991 22301898896642429323271987)
          ·
            refine ⟨33452848344963643984907981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22301898896642429323271987 33452848344963643984907981)
            ·
              refine ⟨12544818129361366494340493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33452848344963643984907981 12544818129361366494340493)
              ·
                refine ⟨4704306798510512435377685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12544818129361366494340493 4704306798510512435377685)
                ·
                  refine ⟨220514381180180270408329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4704306798510512435377685 220514381180180270408329)
                  ·
                    rfl

theorem cell22_1932526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1932526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932526 prefixEnd_1932526 := by exact prefixLift 1932526
  have htrace : WordTrace (prefixWord ++ tailWord_1932526) baseStart_1932526 baseEnd_1932526 := by
    simpa [prefixWord, tailWord_1932526, baseEnd_1932526] using wordTrace_append hprefix tailTrace_1932526
  have hstable : (prefixWord ++ tailWord_1932526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932526).length < 2 ^ (prefixWord ++ tailWord_1932526).sum := by decide
  have hdescent : baseEnd_1932526 < baseStart_1932526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932556 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_1932556 : Nat := 118140960795 + 1932556 * 2 ^ 59
def prefixEnd_1932556 : Nat := 4983230072969 + 3 ^ 40 * 1932556 * 2
def baseEnd_1932556 : Nat := 661553413153630732974895

theorem tailTrace_1932556 : CollatzResearch.WordTrace tailWord_1932556 prefixEnd_1932556 661553413153630732974895 := by
  unfold tailWord_1932556
  simp only [CollatzResearch.WordTrace]
  refine ⟨35243053993343570566472761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46990738657791427421963681 35243053993343570566472761)
  ·
    refine ⟨26432290495007677924854571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35243053993343570566472761 26432290495007677924854571)
    ·
      refine ⟨39648435742511516887281857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26432290495007677924854571 39648435742511516887281857)
      ·
        refine ⟨29736326806883637665461393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39648435742511516887281857 29736326806883637665461393)
        ·
          refine ⟨22302245105162728249096045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29736326806883637665461393 22302245105162728249096045)
          ·
            refine ⟨8363341914436023093411017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22302245105162728249096045 8363341914436023093411017)
            ·
              refine ⟨6272506435827017320058263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8363341914436023093411017 6272506435827017320058263)
              ·
                refine ⟨9408759653740525980087395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272506435827017320058263 9408759653740525980087395)
                ·
                  refine ⟨14113139480610788970131093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9408759653740525980087395 14113139480610788970131093)
                  ·
                    refine ⟨661553413153630732974895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14113139480610788970131093 661553413153630732974895)
                    ·
                      rfl

theorem cell22_1932556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_1932556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932556 prefixEnd_1932556 := by exact prefixLift 1932556
  have htrace : WordTrace (prefixWord ++ tailWord_1932556) baseStart_1932556 baseEnd_1932556 := by
    simpa [prefixWord, tailWord_1932556, baseEnd_1932556] using wordTrace_append hprefix tailTrace_1932556
  have hstable : (prefixWord ++ tailWord_1932556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932556).length < 2 ^ (prefixWord ++ tailWord_1932556).sum := by decide
  have hdescent : baseEnd_1932556 < baseStart_1932556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932558 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_1932558 : Nat := 118140960795 + 1932558 * 2 ^ 59
def prefixEnd_1932558 : Nat := 4983230072969 + 3 ^ 40 * 1932558 * 2
def baseEnd_1932558 : Nat := 661554097794503394424889

theorem tailTrace_1932558 : CollatzResearch.WordTrace tailWord_1932558 prefixEnd_1932558 661554097794503394424889 := by
  unfold tailWord_1932558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810772616584986934314791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46990787288453263649678885 8810772616584986934314791)
  ·
    refine ⟨13216158924877480401472187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810772616584986934314791 13216158924877480401472187)
    ·
      refine ⟨19824238387316220602208281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13216158924877480401472187 19824238387316220602208281)
      ·
        refine ⟨14868178790487165451656211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19824238387316220602208281 14868178790487165451656211)
        ·
          refine ⟨22302268185730748177484317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14868178790487165451656211 22302268185730748177484317)
          ·
            refine ⟨8363350569649030566556619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22302268185730748177484317 8363350569649030566556619)
            ·
              refine ⟨12545025854473545849834929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363350569649030566556619 12545025854473545849834929)
              ·
                refine ⟨9408769390855159387376197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12545025854473545849834929 9408769390855159387376197)
                ·
                  refine ⟨1764144260785342385133037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9408769390855159387376197 1764144260785342385133037)
                  ·
                    refine ⟨661554097794503394424889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764144260785342385133037 661554097794503394424889)
                    ·
                      rfl

theorem cell22_1932558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_1932558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932558 prefixEnd_1932558 := by exact prefixLift 1932558
  have htrace : WordTrace (prefixWord ++ tailWord_1932558) baseStart_1932558 baseEnd_1932558 := by
    simpa [prefixWord, tailWord_1932558, baseEnd_1932558] using wordTrace_append hprefix tailTrace_1932558
  have hstable : (prefixWord ++ tailWord_1932558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932558).length < 2 ^ (prefixWord ++ tailWord_1932558).sum := by decide
  have hdescent : baseEnd_1932558 < baseStart_1932558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932573 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1932573 : Nat := 118140960795 + 1932573 * 2 ^ 59
def prefixEnd_1932573 : Nat := 4983230072969 + 3 ^ 40 * 1932573 * 2
def baseEnd_1932573 : Nat := 661559232601048355299843

theorem tailTrace_1932573 : CollatzResearch.WordTrace tailWord_1932573 prefixEnd_1932573 661559232601048355299843 := by
  unfold tailWord_1932573
  simp only [CollatzResearch.WordTrace]
  refine ⟨70486728027625553036314373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46991152018417035357542915 70486728027625553036314373)
  ·
    refine ⟨13216261505179791194308945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70486728027625553036314373 13216261505179791194308945)
    ·
      refine ⟨9912196128884843395731709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13216261505179791194308945 9912196128884843395731709)
      ·
        refine ⟨3717073548331816273399391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9912196128884843395731709 3717073548331816273399391)
        ·
          refine ⟨5575610322497724410099087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717073548331816273399391 5575610322497724410099087)
          ·
            refine ⟨8363415483746586615148631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575610322497724410099087 8363415483746586615148631)
            ·
              refine ⟨12545123225619879922722947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363415483746586615148631 12545123225619879922722947)
              ·
                refine ⟨18817684838429819884084421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545123225619879922722947 18817684838429819884084421)
                ·
                  refine ⟨3528315907205591228265829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18817684838429819884084421 3528315907205591228265829)
                  ·
                    refine ⟨661559232601048355299843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528315907205591228265829 661559232601048355299843)
                    ·
                      rfl

theorem cell22_1932573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1932573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932573 prefixEnd_1932573 := by exact prefixLift 1932573
  have htrace : WordTrace (prefixWord ++ tailWord_1932573) baseStart_1932573 baseEnd_1932573 := by
    simpa [prefixWord, tailWord_1932573, baseEnd_1932573] using wordTrace_append hprefix tailTrace_1932573
  have hstable : (prefixWord ++ tailWord_1932573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932573).length < 2 ^ (prefixWord ++ tailWord_1932573).sum := by decide
  have hdescent : baseEnd_1932573 < baseStart_1932573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932663 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1932663 : Nat := 118140960795 + 1932663 * 2 ^ 59
def prefixEnd_1932663 : Nat := 4983230072969 + 3 ^ 40 * 1932663 * 2
def baseEnd_1932663 : Nat := 661590041440318120549567

theorem tailTrace_1932663 : CollatzResearch.WordTrace tailWord_1932663 prefixEnd_1932663 661590041440318120549567 := by
  unfold tailWord_1932663
  simp only [CollatzResearch.WordTrace]
  refine ⟨70490010597299498407090643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46993340398199665604727095 70490010597299498407090643)
  ·
    refine ⟨105735015895949247610635965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70490010597299498407090643 105735015895949247610635965)
    ·
      refine ⟨39650630960980967853988487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105735015895949247610635965 39650630960980967853988487)
      ·
        refine ⟨59475946441471451780982731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39650630960980967853988487 59475946441471451780982731)
        ·
          refine ⟨89213919662207177671474097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59475946441471451780982731 89213919662207177671474097)
          ·
            refine ⟨66910439746655383253605573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89213919662207177671474097 66910439746655383253605573)
            ·
              refine ⟨12545707452497884360051045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66910439746655383253605573 12545707452497884360051045)
              ·
                refine ⟨2352320147343353317509571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12545707452497884360051045 2352320147343353317509571)
                ·
                  refine ⟨3528480221015029976264357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352320147343353317509571 3528480221015029976264357)
                  ·
                    refine ⟨661590041440318120549567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528480221015029976264357 661590041440318120549567)
                    ·
                      rfl

theorem cell22_1932663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1932663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932663 prefixEnd_1932663 := by exact prefixLift 1932663
  have htrace : WordTrace (prefixWord ++ tailWord_1932663) baseStart_1932663 baseEnd_1932663 := by
    simpa [prefixWord, tailWord_1932663, baseEnd_1932663] using wordTrace_append hprefix tailTrace_1932663
  have hstable : (prefixWord ++ tailWord_1932663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932663).length < 2 ^ (prefixWord ++ tailWord_1932663).sum := by decide
  have hdescent : baseEnd_1932663 < baseStart_1932663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932680 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_1932680 : Nat := 118140960795 + 1932680 * 2 ^ 59
def prefixEnd_1932680 : Nat := 4983230072969 + 3 ^ 40 * 1932680 * 2
def baseEnd_1932680 : Nat := 661595860887735742874515

theorem tailTrace_1932680 : CollatzResearch.WordTrace tailWord_1932680 prefixEnd_1932680 661595860887735742874515 := by
  unfold tailWord_1932680
  simp only [CollatzResearch.WordTrace]
  refine ⟨35245315319118955155229747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46993753758825273540306329 35245315319118955155229747)
  ·
    refine ⟨52867972978678432732844621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35245315319118955155229747 52867972978678432732844621)
    ·
      refine ⟨19825489867004412274816733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52867972978678432732844621 19825489867004412274816733)
      ·
        refine ⟨7434558700126654603056275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19825489867004412274816733 7434558700126654603056275)
        ·
          refine ⟨11151838050189981904584413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434558700126654603056275 11151838050189981904584413)
          ·
            refine ⟨4181939268821243214219155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11151838050189981904584413 4181939268821243214219155)
            ·
              refine ⟨6272908903231864821328733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181939268821243214219155 6272908903231864821328733)
              ·
                refine ⟨2352340838711949307998275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6272908903231864821328733 2352340838711949307998275)
                ·
                  refine ⟨3528511258067923961997413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352340838711949307998275 3528511258067923961997413)
                  ·
                    refine ⟨661595860887735742874515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528511258067923961997413 661595860887735742874515)
                    ·
                      rfl

theorem cell22_1932680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_1932680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932680 prefixEnd_1932680 := by exact prefixLift 1932680
  have htrace : WordTrace (prefixWord ++ tailWord_1932680) baseStart_1932680 baseEnd_1932680 := by
    simpa [prefixWord, tailWord_1932680, baseEnd_1932680] using wordTrace_append hprefix tailTrace_1932680
  have hstable : (prefixWord ++ tailWord_1932680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932680).length < 2 ^ (prefixWord ++ tailWord_1932680).sum := by decide
  have hdescent : baseEnd_1932680 < baseStart_1932680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932729 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 4]
def baseStart_1932729 : Nat := 118140960795 + 1932729 * 2 ^ 59
def prefixEnd_1932729 : Nat := 4983230072969 + 3 ^ 40 * 1932729 * 2
def baseEnd_1932729 : Nat := 220537544863038649466455

theorem tailTrace_1932729 : CollatzResearch.WordTrace tailWord_1932729 prefixEnd_1932729 220537544863038649466455 := by
  unfold tailWord_1932729
  simp only [CollatzResearch.WordTrace]
  refine ⟨70492417815060391678993241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46994945210040261119328827 70492417815060391678993241)
  ·
    refine ⟨52869313361295293759244931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70492417815060391678993241 52869313361295293759244931)
    ·
      refine ⟨79303970041942940638867397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52869313361295293759244931 79303970041942940638867397)
      ·
        refine ⟨14869494382864301369787637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79303970041942940638867397 14869494382864301369787637)
        ·
          refine ⟨1394015098393528253417591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14869494382864301369787637 1394015098393528253417591)
          ·
            refine ⟨2091022647590292380126387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394015098393528253417591 2091022647590292380126387)
            ·
              refine ⟨3136533971385438570189581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091022647590292380126387 3136533971385438570189581)
              ·
                refine ⟨1176200239269539463821093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3136533971385438570189581 1176200239269539463821093)
                ·
                  refine ⟨220537544863038649466455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176200239269539463821093 220537544863038649466455)
                  ·
                    rfl

theorem cell22_1932729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_1932729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932729 prefixEnd_1932729 := by exact prefixLift 1932729
  have htrace : WordTrace (prefixWord ++ tailWord_1932729) baseStart_1932729 baseEnd_1932729 := by
    simpa [prefixWord, tailWord_1932729, baseEnd_1932729] using wordTrace_append hprefix tailTrace_1932729
  have hstable : (prefixWord ++ tailWord_1932729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932729).length < 2 ^ (prefixWord ++ tailWord_1932729).sum := by decide
  have hdescent : baseEnd_1932729 < baseStart_1932729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932740 : List Nat := [2, 3, 3, 2, 1, 3, 8]
def baseStart_1932740 : Nat := 118140960795 + 1932740 * 2 ^ 59
def prefixEnd_1932740 : Nat := 4983230072969 + 3 ^ 40 * 1932740 * 2
def baseEnd_1932740 : Nat := 24504311115330206902753

theorem tailTrace_1932740 : CollatzResearch.WordTrace tailWord_1932740 prefixEnd_1932740 24504311115330206902753 := by
  unfold tailWord_1932740
  simp only [CollatzResearch.WordTrace]
  refine ⟨35246409509010270278821837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46995212678680360371762449 35246409509010270278821837)
  ·
    refine ⟨13217403565878851354558189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35246409509010270278821837 13217403565878851354558189)
    ·
      refine ⟨4956526337204569257959321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13217403565878851354558189 4956526337204569257959321)
      ·
        refine ⟨3717394752903426943469491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4956526337204569257959321 3717394752903426943469491)
        ·
          refine ⟨5576092129355140415204237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717394752903426943469491 5576092129355140415204237)
          ·
            refine ⟨2091034548508177655701589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5576092129355140415204237 2091034548508177655701589)
            ·
              refine ⟨24504311115330206902753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2091034548508177655701589 24504311115330206902753)
              ·
                rfl

theorem cell22_1932740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 8].length) (baseStart_1932740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932740 prefixEnd_1932740 := by exact prefixLift 1932740
  have htrace : WordTrace (prefixWord ++ tailWord_1932740) baseStart_1932740 baseEnd_1932740 := by
    simpa [prefixWord, tailWord_1932740, baseEnd_1932740] using wordTrace_append hprefix tailTrace_1932740
  have hstable : (prefixWord ++ tailWord_1932740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932740).length < 2 ^ (prefixWord ++ tailWord_1932740).sum := by decide
  have hdescent : baseEnd_1932740 < baseStart_1932740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932802 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1932802 : Nat := 118140960795 + 1932802 * 2 ^ 59
def prefixEnd_1932802 : Nat := 4983230072969 + 3 ^ 40 * 1932802 * 2
def baseEnd_1932802 : Nat := 220545874660322697108047

theorem tailTrace_1932802 : CollatzResearch.WordTrace tailWord_1932802 prefixEnd_1932802 220545874660322697108047 := by
  unfold tailWord_1932802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623770085948981286600165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46996720229197283430933773 17623770085948981286600165)
  ·
    refine ⟨3304456891115433991237531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17623770085948981286600165 3304456891115433991237531)
    ·
      refine ⟨4956685336673150986856297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3304456891115433991237531 4956685336673150986856297)
      ·
        refine ⟨3717514002504863240142223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4956685336673150986856297 3717514002504863240142223)
        ·
          refine ⟨5576271003757294860213335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717514002504863240142223 5576271003757294860213335)
          ·
            refine ⟨8364406505635942290320003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576271003757294860213335 8364406505635942290320003)
            ·
              refine ⟨12546609758453913435480005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364406505635942290320003 12546609758453913435480005)
              ·
                refine ⟨2352489329710108769152501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12546609758453913435480005 2352489329710108769152501)
                ·
                  refine ⟨220545874660322697108047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352489329710108769152501 220545874660322697108047)
                  ·
                    rfl

theorem cell22_1932802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1932802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932802 prefixEnd_1932802 := by exact prefixLift 1932802
  have htrace : WordTrace (prefixWord ++ tailWord_1932802) baseStart_1932802 baseEnd_1932802 := by
    simpa [prefixWord, tailWord_1932802, baseEnd_1932802] using wordTrace_append hprefix tailTrace_1932802
  have hstable : (prefixWord ++ tailWord_1932802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932802).length < 2 ^ (prefixWord ++ tailWord_1932802).sum := by decide
  have hdescent : baseEnd_1932802 < baseStart_1932802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932858 : List Nat := [3, 1, 1, 1, 3, 2, 11]
def baseStart_1932858 : Nat := 118140960795 + 1932858 * 2 ^ 59
def prefixEnd_1932858 : Nat := 4983230072969 + 3 ^ 40 * 1932858 * 2
def baseEnd_1932858 : Nat := 24505807182422318960147

theorem tailTrace_1932858 : CollatzResearch.WordTrace tailWord_1932858 prefixEnd_1932858 24505807182422318960147 := by
  unfold tailWord_1932858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17624280707898261677609807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46998081887728697806959485 17624280707898261677609807)
  ·
    refine ⟨26436421061847392516414711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17624280707898261677609807 26436421061847392516414711)
    ·
      refine ⟨39654631592771088774622067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26436421061847392516414711 39654631592771088774622067)
      ·
        refine ⟨59481947389156633161933101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39654631592771088774622067 59481947389156633161933101)
        ·
          refine ⟨22305730270933737435724913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59481947389156633161933101 22305730270933737435724913)
          ·
            refine ⟨16729297703200303076793685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22305730270933737435724913 16729297703200303076793685)
            ·
              refine ⟨24505807182422318960147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16729297703200303076793685 24505807182422318960147)
              ·
                rfl

theorem cell22_1932858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 11].length) (baseStart_1932858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932858 prefixEnd_1932858 := by exact prefixLift 1932858
  have htrace : WordTrace (prefixWord ++ tailWord_1932858) baseStart_1932858 baseEnd_1932858 := by
    simpa [prefixWord, tailWord_1932858, baseEnd_1932858] using wordTrace_append hprefix tailTrace_1932858
  have hstable : (prefixWord ++ tailWord_1932858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932858).length < 2 ^ (prefixWord ++ tailWord_1932858).sum := by decide
  have hdescent : baseEnd_1932858 < baseStart_1932858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932892 : List Nat := [2, 2, 4, 1, 2, 1, 4, 6]
def baseStart_1932892 : Nat := 118140960795 + 1932892 * 2 ^ 59
def prefixEnd_1932892 : Nat := 4983230072969 + 3 ^ 40 * 1932892 * 2
def baseEnd_1932892 : Nat := 73518714757804206285985

theorem tailTrace_1932892 : CollatzResearch.WordTrace tailWord_1932892 prefixEnd_1932892 73518714757804206285985 := by
  unfold tailWord_1932892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35249181456734935258588465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46998908608979913678117953 35249181456734935258588465)
  ·
    refine ⟨26436886092551201443941349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35249181456734935258588465 26436886092551201443941349)
    ·
      refine ⟨4956916142353350270739003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26436886092551201443941349 4956916142353350270739003)
      ·
        refine ⟨7435374213530025406108505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956916142353350270739003 7435374213530025406108505)
        ·
          refine ⟨5576530660147519054581379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7435374213530025406108505 5576530660147519054581379)
          ·
            refine ⟨8364795990221278581872069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576530660147519054581379 8364795990221278581872069)
            ·
              refine ⟨1568399248166489734101013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8364795990221278581872069 1568399248166489734101013)
              ·
                refine ⟨73518714757804206285985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1568399248166489734101013 73518714757804206285985)
                ·
                  rfl

theorem cell22_1932892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 6].length) (baseStart_1932892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932892 prefixEnd_1932892 := by exact prefixLift 1932892
  have htrace : WordTrace (prefixWord ++ tailWord_1932892) baseStart_1932892 baseEnd_1932892 := by
    simpa [prefixWord, tailWord_1932892, baseEnd_1932892] using wordTrace_append hprefix tailTrace_1932892
  have hstable : (prefixWord ++ tailWord_1932892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932892).length < 2 ^ (prefixWord ++ tailWord_1932892).sum := by decide
  have hdescent : baseEnd_1932892 < baseStart_1932892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932937 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 5]
def baseStart_1932937 : Nat := 118140960795 + 1932937 * 2 ^ 59
def prefixEnd_1932937 : Nat := 4983230072969 + 3 ^ 40 * 1932937 * 2
def baseEnd_1932937 : Nat := 220561279079957579732909

theorem tailTrace_1932937 : CollatzResearch.WordTrace tailWord_1932937 prefixEnd_1932937 220561279079957579732909 := by
  unfold tailWord_1932937
  simp only [CollatzResearch.WordTrace]
  refine ⟨70500004198306843202565065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47000002798871228801710043 70500004198306843202565065)
  ·
    refine ⟨52875003148730132401923799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70500004198306843202565065 52875003148730132401923799)
    ·
      refine ⟨79312504723095198602885699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52875003148730132401923799 79312504723095198602885699)
      ·
        refine ⟨118968757084642797904328549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79312504723095198602885699 118968757084642797904328549)
        ·
          refine ⟨22306641953370524607061603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118968757084642797904328549 22306641953370524607061603)
          ·
            refine ⟨33459962930055786910592405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22306641953370524607061603 33459962930055786910592405)
            ·
              refine ⟨1568435762346365011434019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33459962930055786910592405 1568435762346365011434019)
              ·
                refine ⟨2352653643519547517151029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568435762346365011434019 2352653643519547517151029)
                ·
                  refine ⟨220561279079957579732909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352653643519547517151029 220561279079957579732909)
                  ·
                    rfl

theorem cell22_1932937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_1932937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1932937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1932937 prefixEnd_1932937 := by exact prefixLift 1932937
  have htrace : WordTrace (prefixWord ++ tailWord_1932937) baseStart_1932937 baseEnd_1932937 := by
    simpa [prefixWord, tailWord_1932937, baseEnd_1932937] using wordTrace_append hprefix tailTrace_1932937
  have hstable : (prefixWord ++ tailWord_1932937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932937).length < 2 ^ (prefixWord ++ tailWord_1932937).sum := by decide
  have hdescent : baseEnd_1932937 < baseStart_1932937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933027 : List Nat := [1, 1, 1, 7, 2, 1, 9]
def baseStart_1933027 : Nat := 118140960795 + 1933027 * 2 ^ 59
def prefixEnd_1933027 : Nat := 4983230072969 + 3 ^ 40 * 1933027 * 2
def baseEnd_1933027 : Nat := 24507949854783055720313

theorem tailTrace_1933027 : CollatzResearch.WordTrace tailWord_1933027 prefixEnd_1933027 24507949854783055720313 := by
  unfold tailWord_1933027
  simp only [CollatzResearch.WordTrace]
  refine ⟨70503286767980788573341335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47002191178653859048894223 70503286767980788573341335)
  ·
    refine ⟨105754930151971182860012003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70503286767980788573341335 105754930151971182860012003)
    ·
      refine ⟨158632395227956774290018005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105754930151971182860012003 158632395227956774290018005)
      ·
        refine ⟨3717946763155236897422297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 158632395227956774290018005 3717946763155236897422297)
        ·
          refine ⟨2788460072366427673066723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717946763155236897422297 2788460072366427673066723)
          ·
            refine ⟨4182690108549641509600085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788460072366427673066723 4182690108549641509600085)
            ·
              refine ⟨24507949854783055720313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4182690108549641509600085 24507949854783055720313)
              ·
                rfl

theorem cell22_1933027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 9].length) (baseStart_1933027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933027 prefixEnd_1933027 := by exact prefixLift 1933027
  have htrace : WordTrace (prefixWord ++ tailWord_1933027) baseStart_1933027 baseEnd_1933027 := by
    simpa [prefixWord, tailWord_1933027, baseEnd_1933027] using wordTrace_append hprefix tailTrace_1933027
  have hstable : (prefixWord ++ tailWord_1933027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933027).length < 2 ^ (prefixWord ++ tailWord_1933027).sum := by decide
  have hdescent : baseEnd_1933027 < baseStart_1933027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933031 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1933031 : Nat := 118140960795 + 1933031 * 2 ^ 59
def prefixEnd_1933031 : Nat := 4983230072969 + 3 ^ 40 * 1933031 * 2
def baseEnd_1933031 : Nat := 661716015360887827348439

theorem tailTrace_1933031 : CollatzResearch.WordTrace tailWord_1933031 prefixEnd_1933031 661716015360887827348439 := by
  unfold tailWord_1933031
  simp only [CollatzResearch.WordTrace]
  refine ⟨70503432659966297256486947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47002288439977531504324631 70503432659966297256486947)
  ·
    refine ⟨105755148989949445884730421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70503432659966297256486947 105755148989949445884730421)
    ·
      refine ⟨9914545217807760551693477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105755148989949445884730421 9914545217807760551693477)
      ·
        refine ⟨1858977228338955103442527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9914545217807760551693477 1858977228338955103442527)
        ·
          refine ⟨2788465842508432655163791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858977228338955103442527 2788465842508432655163791)
          ·
            refine ⟨4182698763762648982745687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788465842508432655163791 4182698763762648982745687)
            ·
              refine ⟨6274048145643973474118531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182698763762648982745687 6274048145643973474118531)
              ·
                refine ⟨9411072218465960211177797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274048145643973474118531 9411072218465960211177797)
                ·
                  refine ⟨1764576040962367539595837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9411072218465960211177797 1764576040962367539595837)
                  ·
                    refine ⟨661716015360887827348439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764576040962367539595837 661716015360887827348439)
                    ·
                      rfl

theorem cell22_1933031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1933031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933031 prefixEnd_1933031 := by exact prefixLift 1933031
  have htrace : WordTrace (prefixWord ++ tailWord_1933031) baseStart_1933031 baseEnd_1933031 := by
    simpa [prefixWord, tailWord_1933031, baseEnd_1933031] using wordTrace_append hprefix tailTrace_1933031
  have hstable : (prefixWord ++ tailWord_1933031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933031).length < 2 ^ (prefixWord ++ tailWord_1933031).sum := by decide
  have hdescent : baseEnd_1933031 < baseStart_1933031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933040 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_1933040 : Nat := 118140960795 + 1933040 * 2 ^ 59
def prefixEnd_1933040 : Nat := 4983230072969 + 3 ^ 40 * 1933040 * 2
def baseEnd_1933040 : Nat := 661719096244814803873411

theorem tailTrace_1933040 : CollatzResearch.WordTrace tailWord_1933040 prefixEnd_1933040 661719096244814803873411 := by
  unfold tailWord_1933040
  simp only [CollatzResearch.WordTrace]
  refine ⟨35251880458466845896782287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47002507277955794529043049 35251880458466845896782287)
  ·
    refine ⟨52877820687700268845173431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35251880458466845896782287 52877820687700268845173431)
    ·
      refine ⟨79316731031550403267760147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52877820687700268845173431 79316731031550403267760147)
      ·
        refine ⟨118975096547325604901640221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79316731031550403267760147 118975096547325604901640221)
        ·
          refine ⟨44615661205247101838115083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118975096547325604901640221 44615661205247101838115083)
          ·
            refine ⟨66923491807870652757172625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44615661205247101838115083 66923491807870652757172625)
            ·
              refine ⟨50192618855902989567879469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66923491807870652757172625 50192618855902989567879469)
              ·
                refine ⟨18822232070963621087954801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50192618855902989567879469 18822232070963621087954801)
                ·
                  refine ⟨14116674053222715815966101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18822232070963621087954801 14116674053222715815966101)
                  ·
                    refine ⟨661719096244814803873411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14116674053222715815966101 661719096244814803873411)
                    ·
                      rfl

theorem cell22_1933040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_1933040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933040 prefixEnd_1933040 := by exact prefixLift 1933040
  have htrace : WordTrace (prefixWord ++ tailWord_1933040) baseStart_1933040 baseEnd_1933040 := by
    simpa [prefixWord, tailWord_1933040, baseEnd_1933040] using wordTrace_append hprefix tailTrace_1933040
  have hstable : (prefixWord ++ tailWord_1933040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933040).length < 2 ^ (prefixWord ++ tailWord_1933040).sum := by decide
  have hdescent : baseEnd_1933040 < baseStart_1933040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933093 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_1933093 : Nat := 118140960795 + 1933093 * 2 ^ 59
def prefixEnd_1933093 : Nat := 4983230072969 + 3 ^ 40 * 1933093 * 2
def baseEnd_1933093 : Nat := 661737239227940332298249

theorem tailTrace_1933093 : CollatzResearch.WordTrace tailWord_1933093 prefixEnd_1933093 661737239227940332298249 := by
  unfold tailWord_1933093
  simp only [CollatzResearch.WordTrace]
  refine ⟨70505693985741681845243933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47003795990494454563495955 70505693985741681845243933)
  ·
    refine ⟨26439635244653130691966475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70505693985741681845243933 26439635244653130691966475)
    ·
      refine ⟨39659452866979696037949713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26439635244653130691966475 39659452866979696037949713)
      ·
        refine ⟨29744589650234772028462285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39659452866979696037949713 29744589650234772028462285)
        ·
          refine ⟨11154221118838039510673357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29744589650234772028462285 11154221118838039510673357)
          ·
            refine ⟨4182832919564264816502509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11154221118838039510673357 4182832919564264816502509)
            ·
              refine ⟨1568562344836599306188441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4182832919564264816502509 1568562344836599306188441)
              ·
                refine ⟨1176421758627449479641331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568562344836599306188441 1176421758627449479641331)
                ·
                  refine ⟨1764632637941174219461997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176421758627449479641331 1764632637941174219461997)
                  ·
                    refine ⟨661737239227940332298249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764632637941174219461997 661737239227940332298249)
                    ·
                      rfl

theorem cell22_1933093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_1933093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933093 prefixEnd_1933093 := by exact prefixLift 1933093
  have htrace : WordTrace (prefixWord ++ tailWord_1933093) baseStart_1933093 baseEnd_1933093 := by
    simpa [prefixWord, tailWord_1933093, baseEnd_1933093] using wordTrace_append hprefix tailTrace_1933093
  have hstable : (prefixWord ++ tailWord_1933093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933093).length < 2 ^ (prefixWord ++ tailWord_1933093).sum := by decide
  have hdescent : baseEnd_1933093 < baseStart_1933093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933106 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1933106 : Nat := 118140960795 + 1933106 * 2 ^ 59
def prefixEnd_1933106 : Nat := 4983230072969 + 3 ^ 40 * 1933106 * 2
def baseEnd_1933106 : Nat := 220580563131204210574403

theorem tailTrace_1933106 : CollatzResearch.WordTrace tailWord_1933106 prefixEnd_1933106 220580563131204210574403 := by
  unfold tailWord_1933106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626542033673646266366793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47004112089796390043644781 17626542033673646266366793)
  ·
    refine ⟨13219906525255234699775095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17626542033673646266366793 13219906525255234699775095)
    ·
      refine ⟨19829859787882852049662643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13219906525255234699775095 19829859787882852049662643)
      ·
        refine ⟨29744789681824278074493965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19829859787882852049662643 29744789681824278074493965)
        ·
          refine ⟨11154296130684104277935237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29744789681824278074493965 11154296130684104277935237)
          ·
            refine ⟨2091430524503269552112857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11154296130684104277935237 2091430524503269552112857)
            ·
              refine ⟨1568572893377452164084643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091430524503269552112857 1568572893377452164084643)
              ·
                refine ⟨2352859340066178246126965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568572893377452164084643 2352859340066178246126965)
                ·
                  refine ⟨220580563131204210574403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352859340066178246126965 220580563131204210574403)
                  ·
                    rfl

theorem cell22_1933106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1933106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933106 prefixEnd_1933106 := by exact prefixLift 1933106
  have htrace : WordTrace (prefixWord ++ tailWord_1933106) baseStart_1933106 baseEnd_1933106 := by
    simpa [prefixWord, tailWord_1933106, baseEnd_1933106] using wordTrace_append hprefix tailTrace_1933106
  have hstable : (prefixWord ++ tailWord_1933106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933106).length < 2 ^ (prefixWord ++ tailWord_1933106).sum := by decide
  have hdescent : baseEnd_1933106 < baseStart_1933106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933119 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 3, 4]
def baseStart_1933119 : Nat := 118140960795 + 1933119 * 2 ^ 59
def prefixEnd_1933119 : Nat := 4983230072969 + 3 ^ 40 * 1933119 * 2
def baseEnd_1933119 : Nat := 661746139559284931148169

theorem tailTrace_1933119 : CollatzResearch.WordTrace tailWord_1933119 prefixEnd_1933119 661746139559284931148169 := by
  unfold tailWord_1933119
  simp only [CollatzResearch.WordTrace]
  refine ⟨70506642283647488285690411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47004428189098325523793607 70506642283647488285690411)
  ·
    refine ⟨105759963425471232428535617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70506642283647488285690411 105759963425471232428535617)
    ·
      refine ⟨79319972569103424321401713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105759963425471232428535617 79319972569103424321401713)
      ·
        refine ⟨59489979426827568241051285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79319972569103424321401713 59489979426827568241051285)
        ·
          refine ⟨2788592785632542261299279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59489979426827568241051285 2788592785632542261299279)
          ·
            refine ⟨4182889178448813391948919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788592785632542261299279 4182889178448813391948919)
            ·
              refine ⟨6274333767673220087923379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182889178448813391948919 6274333767673220087923379)
              ·
                refine ⟨9411500651509830131885069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274333767673220087923379 9411500651509830131885069)
                ·
                  refine ⟨3529312744316186299456901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9411500651509830131885069 3529312744316186299456901)
                  ·
                    refine ⟨661746139559284931148169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3529312744316186299456901 661746139559284931148169)
                    ·
                      rfl

theorem cell22_1933119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_1933119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933119 prefixEnd_1933119 := by exact prefixLift 1933119
  have htrace : WordTrace (prefixWord ++ tailWord_1933119) baseStart_1933119 baseEnd_1933119 := by
    simpa [prefixWord, tailWord_1933119, baseEnd_1933119] using wordTrace_append hprefix tailTrace_1933119
  have hstable : (prefixWord ++ tailWord_1933119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933119).length < 2 ^ (prefixWord ++ tailWord_1933119).sum := by decide
  have hdescent : baseEnd_1933119 < baseStart_1933119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933151 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 4]
def baseStart_1933151 : Nat := 118140960795 + 1933151 * 2 ^ 59
def prefixEnd_1933151 : Nat := 4983230072969 + 3 ^ 40 * 1933151 * 2
def baseEnd_1933151 : Nat := 220585697937749171449357

theorem tailTrace_1933151 : CollatzResearch.WordTrace tailWord_1933151 prefixEnd_1933151 220585697937749171449357 := by
  unfold tailWord_1933151
  simp only [CollatzResearch.WordTrace]
  refine ⟨70507809419531557750855307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47005206279687705167236871 70507809419531557750855307)
  ·
    refine ⟨105761714129297336626282961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70507809419531557750855307 105761714129297336626282961)
    ·
      refine ⟨79321285596973002469712221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105761714129297336626282961 79321285596973002469712221)
      ·
        refine ⟨29745482098864875926142083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79321285596973002469712221 29745482098864875926142083)
        ·
          refine ⟨44618223148297313889213125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29745482098864875926142083 44618223148297313889213125)
          ·
            refine ⟨8365916840305746354227461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44618223148297313889213125 8365916840305746354227461)
            ·
              refine ⟨1568609407557327441417649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8365916840305746354227461 1568609407557327441417649)
              ·
                refine ⟨1176457055667995581063237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568609407557327441417649 1176457055667995581063237)
                ·
                  refine ⟨220585697937749171449357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176457055667995581063237 220585697937749171449357)
                  ·
                    rfl

theorem cell22_1933151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 4].length) (baseStart_1933151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933151 prefixEnd_1933151 := by exact prefixLift 1933151
  have htrace : WordTrace (prefixWord ++ tailWord_1933151) baseStart_1933151 baseEnd_1933151 := by
    simpa [prefixWord, tailWord_1933151, baseEnd_1933151] using wordTrace_append hprefix tailTrace_1933151
  have hstable : (prefixWord ++ tailWord_1933151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933151).length < 2 ^ (prefixWord ++ tailWord_1933151).sum := by decide
  have hdescent : baseEnd_1933151 < baseStart_1933151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933166 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1933166 : Nat := 118140960795 + 1933166 * 2 ^ 59
def prefixEnd_1933166 : Nat := 4983230072969 + 3 ^ 40 * 1933166 * 2
def baseEnd_1933166 : Nat := 661762228619792475223025

theorem tailTrace_1933166 : CollatzResearch.WordTrace tailWord_1933166 prefixEnd_1933166 661762228619792475223025 := by
  unfold tailWord_1933166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813544564309651914081419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47005571009651476875100901 8813544564309651914081419)
  ·
    refine ⟨13220316846464477871122129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813544564309651914081419 13220316846464477871122129)
    ·
      refine ⟨9915237634848358403341597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13220316846464477871122129 9915237634848358403341597)
      ·
        refine ⟨3718214113068134401253099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9915237634848358403341597 3718214113068134401253099)
        ·
          refine ⟨5577321169602201601879649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718214113068134401253099 5577321169602201601879649)
          ·
            refine ⟨4182990877201651201409737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5577321169602201601879649 4182990877201651201409737)
            ·
              refine ⟨3137243157901238401057303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182990877201651201409737 3137243157901238401057303)
              ·
                refine ⟨4705864736851857601585955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137243157901238401057303 4705864736851857601585955)
                ·
                  refine ⟨7058797105277786402378933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705864736851857601585955 7058797105277786402378933)
                  ·
                    refine ⟨661762228619792475223025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7058797105277786402378933 661762228619792475223025)
                    ·
                      rfl

theorem cell22_1933166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1933166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933166 prefixEnd_1933166 := by exact prefixLift 1933166
  have htrace : WordTrace (prefixWord ++ tailWord_1933166) baseStart_1933166 baseEnd_1933166 := by
    simpa [prefixWord, tailWord_1933166, baseEnd_1933166] using wordTrace_append hprefix tailTrace_1933166
  have hstable : (prefixWord ++ tailWord_1933166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933166).length < 2 ^ (prefixWord ++ tailWord_1933166).sum := by decide
  have hdescent : baseEnd_1933166 < baseStart_1933166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933245 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1933245 : Nat := 118140960795 + 1933245 * 2 ^ 59
def prefixEnd_1933245 : Nat := 4983230072969 + 3 ^ 40 * 1933245 * 2
def baseEnd_1933245 : Nat := 661789271934262602497783

theorem tailTrace_1933245 : CollatzResearch.WordTrace tailWord_1933245 prefixEnd_1933245 661789271934262602497783 := by
  unfold tailWord_1933245
  simp only [CollatzResearch.WordTrace]
  refine ⟨70511237881191011804777189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47007491920794007869851459 70511237881191011804777189)
  ·
    refine ⟨13220857102723314713395723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70511237881191011804777189 13220857102723314713395723)
    ·
      refine ⟨19831285654084972070093585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220857102723314713395723 19831285654084972070093585)
      ·
        refine ⟨14873464240563729052570189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19831285654084972070093585 14873464240563729052570189)
        ·
          refine ⟨5577549090211398394713821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14873464240563729052570189 5577549090211398394713821)
          ·
            refine ⟨2091580908829274398017683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5577549090211398394713821 2091580908829274398017683)
            ·
              refine ⟨3137371363243911597026525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091580908829274398017683 3137371363243911597026525)
              ·
                refine ⟨1176514261216466848884947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3137371363243911597026525 1176514261216466848884947)
                ·
                  refine ⟨1764771391824700273327421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176514261216466848884947 1764771391824700273327421)
                  ·
                    refine ⟨661789271934262602497783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764771391824700273327421 661789271934262602497783)
                    ·
                      rfl

theorem cell22_1933245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1933245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933245 prefixEnd_1933245 := by exact prefixLift 1933245
  have htrace : WordTrace (prefixWord ++ tailWord_1933245) baseStart_1933245 baseEnd_1933245 := by
    simpa [prefixWord, tailWord_1933245, baseEnd_1933245] using wordTrace_append hprefix tailTrace_1933245
  have hstable : (prefixWord ++ tailWord_1933245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933245).length < 2 ^ (prefixWord ++ tailWord_1933245).sum := by decide
  have hdescent : baseEnd_1933245 < baseStart_1933245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933284 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1933284 : Nat := 118140960795 + 1933284 * 2 ^ 59
def prefixEnd_1933284 : Nat := 4983230072969 + 3 ^ 40 * 1933284 * 2
def baseEnd_1933284 : Nat := 661802622431279500772663

theorem tailTrace_1933284 : CollatzResearch.WordTrace tailWord_1933284 prefixEnd_1933284 661802622431279500772663 := by
  unfold tailWord_1933284
  simp only [CollatzResearch.WordTrace]
  refine ⟨35256330164024860732723453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47008440218699814310297937 35256330164024860732723453)
  ·
    refine ⟨13221123811509322774771295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35256330164024860732723453 13221123811509322774771295)
    ·
      refine ⟨19831685717263984162156943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13221123811509322774771295 19831685717263984162156943)
      ·
        refine ⟨29747528575895976243235415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19831685717263984162156943 29747528575895976243235415)
        ·
          refine ⟨44621292863843964364853123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29747528575895976243235415 44621292863843964364853123)
          ·
            refine ⟨66931939295765946547279685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44621292863843964364853123 66931939295765946547279685)
            ·
              refine ⟨12549738617956114977614941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66931939295765946547279685 12549738617956114977614941)
              ·
                refine ⟨4706151981733543116605603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12549738617956114977614941 4706151981733543116605603)
                ·
                  refine ⟨7059227972600314674908405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706151981733543116605603 7059227972600314674908405)
                  ·
                    refine ⟨661802622431279500772663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7059227972600314674908405 661802622431279500772663)
                    ·
                      rfl

theorem cell22_1933284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1933284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933284 prefixEnd_1933284 := by exact prefixLift 1933284
  have htrace : WordTrace (prefixWord ++ tailWord_1933284) baseStart_1933284 baseEnd_1933284 := by
    simpa [prefixWord, tailWord_1933284, baseEnd_1933284] using wordTrace_append hprefix tailTrace_1933284
  have hstable : (prefixWord ++ tailWord_1933284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933284).length < 2 ^ (prefixWord ++ tailWord_1933284).sum := by decide
  have hdescent : baseEnd_1933284 < baseStart_1933284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933314 : List Nat := [3, 4, 1, 14]
def baseStart_1933314 : Nat := 118140960795 + 1933314 * 2 ^ 59
def prefixEnd_1933314 : Nat := 4983230072969 + 3 ^ 40 * 1933314 * 2
def baseEnd_1933314 : Nat := 907836614601329797699

theorem tailTrace_1933314 : CollatzResearch.WordTrace tailWord_1933314 prefixEnd_1933314 907836614601329797699 := by
  unfold tailWord_1933314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628438629485259147259749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47009169678627357726025997 17628438629485259147259749)
  ·
    refine ⟨3305332243028486090111203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17628438629485259147259749 3305332243028486090111203)
    ·
      refine ⟨4957998364542729135166805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3305332243028486090111203 4957998364542729135166805)
      ·
        refine ⟨907836614601329797699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 4957998364542729135166805 907836614601329797699)
        ·
          rfl

theorem cell22_1933314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 14].length) (baseStart_1933314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933314 prefixEnd_1933314 := by exact prefixLift 1933314
  have htrace : WordTrace (prefixWord ++ tailWord_1933314) baseStart_1933314 baseEnd_1933314 := by
    simpa [prefixWord, tailWord_1933314, baseEnd_1933314] using wordTrace_append hprefix tailTrace_1933314
  have hstable : (prefixWord ++ tailWord_1933314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933314).length < 2 ^ (prefixWord ++ tailWord_1933314).sum := by decide
  have hdescent : baseEnd_1933314 < baseStart_1933314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933348 : List Nat := [2, 3, 1, 4, 2, 1, 3, 6]
def baseStart_1933348 : Nat := 118140960795 + 1933348 * 2 ^ 59
def prefixEnd_1933348 : Nat := 4983230072969 + 3 ^ 40 * 1933348 * 2
def baseEnd_1933348 : Nat := 73536058993244963019163

theorem tailTrace_1933348 : CollatzResearch.WordTrace tailWord_1933348 prefixEnd_1933348 73536058993244963019163 := by
  unfold tailWord_1933348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35257497299908930197888349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47009996399878573597184465 35257497299908930197888349)
  ·
    refine ⟨13221561487465848824208131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35257497299908930197888349 13221561487465848824208131)
    ·
      refine ⟨19832342231198773236312197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13221561487465848824208131 19832342231198773236312197)
      ·
        refine ⟨3718564168349769981808537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19832342231198773236312197 3718564168349769981808537)
        ·
          refine ⟨2788923126262327486356403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3718564168349769981808537 2788923126262327486356403)
          ·
            refine ⟨4183384689393491229534605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788923126262327486356403 4183384689393491229534605)
            ·
              refine ⟨1568769258522559211075477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4183384689393491229534605 1568769258522559211075477)
              ·
                refine ⟨73536058993244963019163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1568769258522559211075477 73536058993244963019163)
                ·
                  rfl

theorem cell22_1933348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 6].length) (baseStart_1933348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933348 prefixEnd_1933348 := by exact prefixLift 1933348
  have htrace : WordTrace (prefixWord ++ tailWord_1933348) baseStart_1933348 baseEnd_1933348 := by
    simpa [prefixWord, tailWord_1933348, baseEnd_1933348] using wordTrace_append hprefix tailTrace_1933348
  have hstable : (prefixWord ++ tailWord_1933348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933348).length < 2 ^ (prefixWord ++ tailWord_1933348).sum := by decide
  have hdescent : baseEnd_1933348 < baseStart_1933348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933363 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 1, 3]
def baseStart_1933363 : Nat := 118140960795 + 1933363 * 2 ^ 59
def prefixEnd_1933363 : Nat := 4983230072969 + 3 ^ 40 * 1933363 * 2
def baseEnd_1933363 : Nat := 661829665745749628047421

theorem tailTrace_1933363 : CollatzResearch.WordTrace tailWord_1933363 prefixEnd_1933363 661829665745749628047421 := by
  unfold tailWord_1933363
  simp only [CollatzResearch.WordTrace]
  refine ⟨70515541694763517957572743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47010361129842345305048495 70515541694763517957572743)
  ·
    refine ⟨105773312542145276936359115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70515541694763517957572743 105773312542145276936359115)
    ·
      refine ⟨158659968813217915404538673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105773312542145276936359115 158659968813217915404538673)
      ·
        refine ⟨118994976609913436553404005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158659968813217915404538673 118994976609913436553404005)
        ·
          refine ⟨22311558114358769353763251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118994976609913436553404005 22311558114358769353763251)
          ·
            refine ⟨33467337171538154030644877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22311558114358769353763251 33467337171538154030644877)
            ·
              refine ⟨12550251439326807761491829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33467337171538154030644877 12550251439326807761491829)
              ·
                refine ⟨1176586072436888227639859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12550251439326807761491829 1176586072436888227639859)
                ·
                  refine ⟨1764879108655332341459789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176586072436888227639859 1764879108655332341459789)
                  ·
                    refine ⟨661829665745749628047421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764879108655332341459789 661829665745749628047421)
                    ·
                      rfl

theorem cell22_1933363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 3].length) (baseStart_1933363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933363 prefixEnd_1933363 := by exact prefixLift 1933363
  have htrace : WordTrace (prefixWord ++ tailWord_1933363) baseStart_1933363 baseEnd_1933363 := by
    simpa [prefixWord, tailWord_1933363, baseEnd_1933363] using wordTrace_append hprefix tailTrace_1933363
  have hstable : (prefixWord ++ tailWord_1933363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933363).length < 2 ^ (prefixWord ++ tailWord_1933363).sum := by decide
  have hdescent : baseEnd_1933363 < baseStart_1933363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933376 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_1933376 : Nat := 118140960795 + 1933376 * 2 ^ 59
def prefixEnd_1933376 : Nat := 4983230072969 + 3 ^ 40 * 1933376 * 2
def baseEnd_1933376 : Nat := 220611371970473975824127

theorem tailTrace_1933376 : CollatzResearch.WordTrace tailWord_1933376 prefixEnd_1933376 220611371970473975824127 := by
  unfold tailWord_1933376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35258007921858210588897991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47010677229144280785197321 35258007921858210588897991)
  ·
    refine ⟨52887011882787315883346987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35258007921858210588897991 52887011882787315883346987)
    ·
      refine ⟨79330517824180973825020481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52887011882787315883346987 79330517824180973825020481)
      ·
        refine ⟨59497888368135730368765361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79330517824180973825020481 59497888368135730368765361)
        ·
          refine ⟨44623416276101797776574021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59497888368135730368765361 44623416276101797776574021)
          ·
            refine ⟨8366890551769087083107629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44623416276101797776574021 8366890551769087083107629)
            ·
              refine ⟨3137583956913407656165361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8366890551769087083107629 3137583956913407656165361)
              ·
                refine ⟨2353187967685055742124021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137583956913407656165361 2353187967685055742124021)
                ·
                  refine ⟨220611371970473975824127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353187967685055742124021 220611371970473975824127)
                  ·
                    rfl

theorem cell22_1933376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_1933376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933376 prefixEnd_1933376 := by exact prefixLift 1933376
  have htrace : WordTrace (prefixWord ++ tailWord_1933376) baseStart_1933376 baseEnd_1933376 := by
    simpa [prefixWord, tailWord_1933376, baseEnd_1933376] using wordTrace_append hprefix tailTrace_1933376
  have hstable : (prefixWord ++ tailWord_1933376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933376).length < 2 ^ (prefixWord ++ tailWord_1933376).sum := by decide
  have hdescent : baseEnd_1933376 < baseStart_1933376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933434 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1933434 : Nat := 118140960795 + 1933434 * 2 ^ 59
def prefixEnd_1933434 : Nat := 4983230072969 + 3 ^ 40 * 1933434 * 2
def baseEnd_1933434 : Nat := 661853970496729109522203

theorem tailTrace_1933434 : CollatzResearch.WordTrace tailWord_1933434 prefixEnd_1933434 661853970496729109522203 := by
  unfold tailWord_1933434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629532819376574270851839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47012087518337531388938237 17629532819376574270851839)
  ·
    refine ⟨26444299229064861406277759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17629532819376574270851839 26444299229064861406277759)
    ·
      refine ⟨39666448843597292109416639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26444299229064861406277759 39666448843597292109416639)
      ·
        refine ⟨59499673265395938164124959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39666448843597292109416639 59499673265395938164124959)
        ·
          refine ⟨89249509898093907246187439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59499673265395938164124959 89249509898093907246187439)
          ·
            refine ⟨133874264847140860869281159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89249509898093907246187439 133874264847140860869281159)
            ·
              refine ⟨200811397270711291303921739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133874264847140860869281159 200811397270711291303921739)
              ·
                refine ⟨301217095906066936955882609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200811397270711291303921739 301217095906066936955882609)
                ·
                  refine ⟨225912821929550202716911957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301217095906066936955882609 225912821929550202716911957)
                  ·
                    refine ⟨661853970496729109522203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 225912821929550202716911957 661853970496729109522203)
                    ·
                      rfl

theorem cell22_1933434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1933434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933434 prefixEnd_1933434 := by exact prefixLift 1933434
  have htrace : WordTrace (prefixWord ++ tailWord_1933434) baseStart_1933434 baseEnd_1933434 := by
    simpa [prefixWord, tailWord_1933434, baseEnd_1933434] using wordTrace_append hprefix tailTrace_1933434
  have hstable : (prefixWord ++ tailWord_1933434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933434).length < 2 ^ (prefixWord ++ tailWord_1933434).sum := by decide
  have hdescent : baseEnd_1933434 < baseStart_1933434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933468 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_1933468 : Nat := 118140960795 + 1933468 * 2 ^ 59
def prefixEnd_1933468 : Nat := 4983230072969 + 3 ^ 40 * 1933468 * 2
def baseEnd_1933468 : Nat := 661865609391564354172099

theorem tailTrace_1933468 : CollatzResearch.WordTrace tailWord_1933468 prefixEnd_1933468 661865609391564354172099 := by
  unfold tailWord_1933468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259685679691560445072529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47012914239588747260096705 35259685679691560445072529)
  ·
    refine ⟨26444764259768670333804397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35259685679691560445072529 26444764259768670333804397)
    ·
      refine ⟨9916786597413251375176649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26444764259768670333804397 9916786597413251375176649)
      ·
        refine ⟨7437589948059938531382487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9916786597413251375176649 7437589948059938531382487)
        ·
          refine ⟨11156384922089907797073731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437589948059938531382487 11156384922089907797073731)
          ·
            refine ⟨16734577383134861695610597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156384922089907797073731 16734577383134861695610597)
            ·
              refine ⟨3137733259337786567926987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16734577383134861695610597 3137733259337786567926987)
              ·
                refine ⟨4706599889006679851890481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137733259337786567926987 4706599889006679851890481)
                ·
                  refine ⟨3529949916755009888917861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4706599889006679851890481 3529949916755009888917861)
                  ·
                    refine ⟨661865609391564354172099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3529949916755009888917861 661865609391564354172099)
                    ·
                      rfl

theorem cell22_1933468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_1933468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933468 prefixEnd_1933468 := by exact prefixLift 1933468
  have htrace : WordTrace (prefixWord ++ tailWord_1933468) baseStart_1933468 baseEnd_1933468 := by
    simpa [prefixWord, tailWord_1933468, baseEnd_1933468] using wordTrace_append hprefix tailTrace_1933468
  have hstable : (prefixWord ++ tailWord_1933468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933468).length < 2 ^ (prefixWord ++ tailWord_1933468).sum := by decide
  have hdescent : baseEnd_1933468 < baseStart_1933468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933470 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1933470 : Nat := 118140960795 + 1933470 * 2 ^ 59
def prefixEnd_1933470 : Nat := 4983230072969 + 3 ^ 40 * 1933470 * 2
def baseEnd_1933470 : Nat := 661866294032437015622093

theorem tailTrace_1933470 : CollatzResearch.WordTrace tailWord_1933470 prefixEnd_1933470 661866294032437015622093 := by
  unfold tailWord_1933470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814930538171984403964733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47012962870250583487811909 8814930538171984403964733)
  ·
    refine ⟨3305598951814494151486775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8814930538171984403964733 3305598951814494151486775)
    ·
      refine ⟨4958398427721741227230163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3305598951814494151486775 4958398427721741227230163)
      ·
        refine ⟨7437597641582611840845245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958398427721741227230163 7437597641582611840845245)
        ·
          refine ⟨2789099115593479440316967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7437597641582611840845245 2789099115593479440316967)
          ·
            refine ⟨4183648673390219160475451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789099115593479440316967 4183648673390219160475451)
            ·
              refine ⟨6275473010085328740713177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183648673390219160475451 6275473010085328740713177)
              ·
                refine ⟨4706604757563996555534883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275473010085328740713177 4706604757563996555534883)
                ·
                  refine ⟨7059907136345994833302325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706604757563996555534883 7059907136345994833302325)
                  ·
                    refine ⟨661866294032437015622093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7059907136345994833302325 661866294032437015622093)
                    ·
                      rfl

theorem cell22_1933470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1933470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933470 prefixEnd_1933470 := by exact prefixLift 1933470
  have htrace : WordTrace (prefixWord ++ tailWord_1933470) baseStart_1933470 baseEnd_1933470 := by
    simpa [prefixWord, tailWord_1933470, baseEnd_1933470] using wordTrace_append hprefix tailTrace_1933470
  have hstable : (prefixWord ++ tailWord_1933470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933470).length < 2 ^ (prefixWord ++ tailWord_1933470).sum := by decide
  have hdescent : baseEnd_1933470 < baseStart_1933470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933489 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 4]
def baseStart_1933489 : Nat := 118140960795 + 1933489 * 2 ^ 59
def prefixEnd_1933489 : Nat := 4983230072969 + 3 ^ 40 * 1933489 * 2
def baseEnd_1933489 : Nat := 220624266040242433132345

theorem tailTrace_1933489 : CollatzResearch.WordTrace tailWord_1933489 prefixEnd_1933489 220624266040242433132345 := by
  unfold tailWord_1933489
  simp only [CollatzResearch.WordTrace]
  refine ⟨70520137292307041476659521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47013424861538027651106347 70520137292307041476659521)
  ·
    refine ⟨52890102969230281107494641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70520137292307041476659521 52890102969230281107494641)
    ·
      refine ⟨39667577226922710830620981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52890102969230281107494641 39667577226922710830620981)
      ·
        refine ⟨3718835365024004140370717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39667577226922710830620981 3718835365024004140370717)
        ·
          refine ⟨1394563261884001552639019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3718835365024004140370717 1394563261884001552639019)
          ·
            refine ⟨2091844892826002328958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394563261884001552639019 2091844892826002328958529)
            ·
              refine ⟨1568883669619501746718897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091844892826002328958529 1568883669619501746718897)
              ·
                refine ⟨1176662752214626310039173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568883669619501746718897 1176662752214626310039173)
                ·
                  refine ⟨220624266040242433132345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176662752214626310039173 220624266040242433132345)
                  ·
                    rfl

theorem cell22_1933489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_1933489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933489 prefixEnd_1933489 := by exact prefixLift 1933489
  have htrace : WordTrace (prefixWord ++ tailWord_1933489) baseStart_1933489 baseEnd_1933489 := by
    simpa [prefixWord, tailWord_1933489, baseEnd_1933489] using wordTrace_append hprefix tailTrace_1933489
  have hstable : (prefixWord ++ tailWord_1933489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933489).length < 2 ^ (prefixWord ++ tailWord_1933489).sum := by decide
  have hdescent : baseEnd_1933489 < baseStart_1933489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933500 : List Nat := [2, 2, 2, 3, 4, 1, 1, 7]
def baseStart_1933500 : Nat := 118140960795 + 1933500 * 2 ^ 59
def prefixEnd_1933500 : Nat := 4983230072969 + 3 ^ 40 * 1933500 * 2
def baseEnd_1933500 : Nat := 73541840405058548596889

theorem tailTrace_1933500 : CollatzResearch.WordTrace tailWord_1933500 prefixEnd_1933500 73541840405058548596889 := by
  unfold tailWord_1933500
  simp only [CollatzResearch.WordTrace]
  refine ⟨35260269247633595177654977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47013692330178126903539969 35260269247633595177654977)
  ·
    refine ⟨26445201935725196383241233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35260269247633595177654977 26445201935725196383241233)
    ·
      refine ⟨19833901451793897287430925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26445201935725196383241233 19833901451793897287430925)
      ·
        refine ⟨7437713044422711482786597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19833901451793897287430925 7437713044422711482786597)
        ·
          refine ⟨1394571195829258403022487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7437713044422711482786597 1394571195829258403022487)
          ·
            refine ⟨2091856793743887604533731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394571195829258403022487 2091856793743887604533731)
            ·
              refine ⟨3137785190615831406800597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091856793743887604533731 3137785190615831406800597)
              ·
                refine ⟨73541840405058548596889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3137785190615831406800597 73541840405058548596889)
                ·
                  rfl

theorem cell22_1933500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 7].length) (baseStart_1933500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933500 prefixEnd_1933500 := by exact prefixLift 1933500
  have htrace : WordTrace (prefixWord ++ tailWord_1933500) baseStart_1933500 baseEnd_1933500 := by
    simpa [prefixWord, tailWord_1933500, baseEnd_1933500] using wordTrace_append hprefix tailTrace_1933500
  have hstable : (prefixWord ++ tailWord_1933500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933500).length < 2 ^ (prefixWord ++ tailWord_1933500).sum := by decide
  have hdescent : baseEnd_1933500 < baseStart_1933500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933538 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1933538 : Nat := 118140960795 + 1933538 * 2 ^ 59
def prefixEnd_1933538 : Nat := 4983230072969 + 3 ^ 40 * 1933538 * 2
def baseEnd_1933538 : Nat := 661889571822107504921885

theorem tailTrace_1933538 : CollatzResearch.WordTrace tailWord_1933538 prefixEnd_1933538 661889571822107504921885 := by
  unfold tailWord_1933538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17630481117282380711298317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47014616312753015230128845 17630481117282380711298317)
  ·
    refine ⟨6611430418980892766736869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17630481117282380711298317 6611430418980892766736869)
    ·
      refine ⟨1239643203558917393763163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6611430418980892766736869 1239643203558917393763163)
      ·
        refine ⟨1859464805338376090644745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239643203558917393763163 1859464805338376090644745)
        ·
          refine ⟨1394598604003782067983559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859464805338376090644745 1394598604003782067983559)
          ·
            refine ⟨2091897906005673101975339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394598604003782067983559 2091897906005673101975339)
            ·
              refine ⟨3137846859008509652963009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091897906005673101975339 3137846859008509652963009)
              ·
                refine ⟨2353385144256382239722257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137846859008509652963009 2353385144256382239722257)
                ·
                  refine ⟨1765038858192286679791693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2353385144256382239722257 1765038858192286679791693)
                  ·
                    refine ⟨661889571822107504921885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765038858192286679791693 661889571822107504921885)
                    ·
                      rfl

theorem cell22_1933538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1933538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933538 prefixEnd_1933538 := by exact prefixLift 1933538
  have htrace : WordTrace (prefixWord ++ tailWord_1933538) baseStart_1933538 baseEnd_1933538 := by
    simpa [prefixWord, tailWord_1933538, baseEnd_1933538] using wordTrace_append hprefix tailTrace_1933538
  have hstable : (prefixWord ++ tailWord_1933538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933538).length < 2 ^ (prefixWord ++ tailWord_1933538).sum := by decide
  have hdescent : baseEnd_1933538 < baseStart_1933538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933543 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1933543 : Nat := 118140960795 + 1933543 * 2 ^ 59
def prefixEnd_1933543 : Nat := 4983230072969 + 3 ^ 40 * 1933543 * 2
def baseEnd_1933543 : Nat := 661891283424289158546869

theorem tailTrace_1933543 : CollatzResearch.WordTrace tailWord_1933543 prefixEnd_1933543 661891283424289158546869 := by
  unfold tailWord_1933543
  simp only [CollatzResearch.WordTrace]
  refine ⟨70522106834111408699125283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47014737889407605799416855 70522106834111408699125283)
  ·
    refine ⟨105783160251167113048687925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70522106834111408699125283 105783160251167113048687925)
    ·
      refine ⟨9917171273546916848314493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105783160251167113048687925 9917171273546916848314493)
      ·
        refine ⟨3718939227580093818117935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9917171273546916848314493 3718939227580093818117935)
        ·
          refine ⟨5578408841370140727176903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718939227580093818117935 5578408841370140727176903)
          ·
            refine ⟨8367613262055211090765355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578408841370140727176903 8367613262055211090765355)
            ·
              refine ⟨12551419893082816636148033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367613262055211090765355 12551419893082816636148033)
              ·
                refine ⟨9413564919812112477111025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12551419893082816636148033 9413564919812112477111025)
                ·
                  refine ⟨7060173689859084357833269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9413564919812112477111025 7060173689859084357833269)
                  ·
                    refine ⟨661891283424289158546869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7060173689859084357833269 661891283424289158546869)
                    ·
                      rfl

theorem cell22_1933543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1933543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933543 prefixEnd_1933543 := by exact prefixLift 1933543
  have htrace : WordTrace (prefixWord ++ tailWord_1933543) baseStart_1933543 baseEnd_1933543 := by
    simpa [prefixWord, tailWord_1933543, baseEnd_1933543] using wordTrace_append hprefix tailTrace_1933543
  have hstable : (prefixWord ++ tailWord_1933543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933543).length < 2 ^ (prefixWord ++ tailWord_1933543).sum := by decide
  have hdescent : baseEnd_1933543 < baseStart_1933543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933558 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1933558 : Nat := 118140960795 + 1933558 * 2 ^ 59
def prefixEnd_1933558 : Nat := 4983230072969 + 3 ^ 40 * 1933558 * 2
def baseEnd_1933558 : Nat := 661896418230834119421823

theorem tailTrace_1933558 : CollatzResearch.WordTrace tailWord_1933558 prefixEnd_1933558 661896418230834119421823 := by
  unfold tailWord_1933558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407665870566066641307583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47015102619371377507280885 4407665870566066641307583)
  ·
    refine ⟨6611498805849099961961375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407665870566066641307583 6611498805849099961961375)
    ·
      refine ⟨9917248208773649942942063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6611498805849099961961375 9917248208773649942942063)
      ·
        refine ⟨14875872313160474914413095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9917248208773649942942063 14875872313160474914413095)
        ·
          refine ⟨22313808469740712371619643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14875872313160474914413095 22313808469740712371619643)
          ·
            refine ⟨33470712704611068557429465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22313808469740712371619643 33470712704611068557429465)
            ·
              refine ⟨25103034528458301418072099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33470712704611068557429465 25103034528458301418072099)
              ·
                refine ⟨37654551792687452127108149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25103034528458301418072099 37654551792687452127108149)
                ·
                  refine ⟨3530114230564448636916389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37654551792687452127108149 3530114230564448636916389)
                  ·
                    refine ⟨661896418230834119421823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530114230564448636916389 661896418230834119421823)
                    ·
                      rfl

theorem cell22_1933558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1933558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933558 prefixEnd_1933558 := by exact prefixLift 1933558
  have htrace : WordTrace (prefixWord ++ tailWord_1933558) baseStart_1933558 baseEnd_1933558 := by
    simpa [prefixWord, tailWord_1933558, baseEnd_1933558] using wordTrace_append hprefix tailTrace_1933558
  have hstable : (prefixWord ++ tailWord_1933558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933558).length < 2 ^ (prefixWord ++ tailWord_1933558).sum := by decide
  have hdescent : baseEnd_1933558 < baseStart_1933558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933601 : List Nat := [1, 2, 3, 2, 1, 1, 12]
def baseStart_1933601 : Nat := 118140960795 + 1933601 * 2 ^ 59
def prefixEnd_1933601 : Nat := 4983230072969 + 3 ^ 40 * 1933601 * 2
def baseEnd_1933601 : Nat := 24515227333688753355433

theorem tailTrace_1933601 : CollatzResearch.WordTrace tailWord_1933601 prefixEnd_1933601 24515227333688753355433 := by
  unfold tailWord_1933601
  simp only [CollatzResearch.WordTrace]
  refine ⟨70524222267901284604736657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47016148178600856403157771 70524222267901284604736657)
  ·
    refine ⟨52893166700925963453552493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70524222267901284604736657 52893166700925963453552493)
    ·
      refine ⟨19834937512847236295082185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52893166700925963453552493 19834937512847236295082185)
      ·
        refine ⟨14876203134635427221311639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19834937512847236295082185 14876203134635427221311639)
        ·
          refine ⟨22314304701953140831967459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14876203134635427221311639 22314304701953140831967459)
          ·
            refine ⟨33471457052929711247951189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22314304701953140831967459 33471457052929711247951189)
            ·
              refine ⟨24515227333688753355433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 33471457052929711247951189 24515227333688753355433)
              ·
                rfl

theorem cell22_1933601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 12].length) (baseStart_1933601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933601 prefixEnd_1933601 := by exact prefixLift 1933601
  have htrace : WordTrace (prefixWord ++ tailWord_1933601) baseStart_1933601 baseEnd_1933601 := by
    simpa [prefixWord, tailWord_1933601, baseEnd_1933601] using wordTrace_append hprefix tailTrace_1933601
  have hstable : (prefixWord ++ tailWord_1933601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933601).length < 2 ^ (prefixWord ++ tailWord_1933601).sum := by decide
  have hdescent : baseEnd_1933601 < baseStart_1933601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933603 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 2, 4]
def baseStart_1933603 : Nat := 118140960795 + 1933603 * 2 ^ 59
def prefixEnd_1933603 : Nat := 4983230072969 + 3 ^ 40 * 1933603 * 2
def baseEnd_1933603 : Nat := 661911822650469002046685

theorem tailTrace_1933603 : CollatzResearch.WordTrace tailWord_1933603 prefixEnd_1933603 661911822650469002046685 := by
  unfold tailWord_1933603
  simp only [CollatzResearch.WordTrace]
  refine ⟨70524295213894038946309463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47016196809262692630872975 70524295213894038946309463)
  ·
    refine ⟨105786442820841058419464195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70524295213894038946309463 105786442820841058419464195)
    ·
      refine ⟨158679664231261587629196293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105786442820841058419464195 158679664231261587629196293)
      ·
        refine ⟨29752437043361547680474305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158679664231261587629196293 29752437043361547680474305)
        ·
          refine ⟨22314327782521160760355729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29752437043361547680474305 22314327782521160760355729)
          ·
            refine ⟨16735745836890870570266797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22314327782521160760355729 16735745836890870570266797)
            ·
              refine ⟨6275904688834076463850049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16735745836890870570266797 6275904688834076463850049)
              ·
                refine ⟨4706928516625557347887537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275904688834076463850049 4706928516625557347887537)
                ·
                  refine ⟨3530196387469168010915653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4706928516625557347887537 3530196387469168010915653)
                  ·
                    refine ⟨661911822650469002046685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530196387469168010915653 661911822650469002046685)
                    ·
                      rfl

theorem cell22_1933603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_1933603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933603 prefixEnd_1933603 := by exact prefixLift 1933603
  have htrace : WordTrace (prefixWord ++ tailWord_1933603) baseStart_1933603 baseEnd_1933603 := by
    simpa [prefixWord, tailWord_1933603, baseEnd_1933603] using wordTrace_append hprefix tailTrace_1933603
  have hstable : (prefixWord ++ tailWord_1933603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933603).length < 2 ^ (prefixWord ++ tailWord_1933603).sum := by decide
  have hdescent : baseEnd_1933603 < baseStart_1933603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933616 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_1933616 : Nat := 118140960795 + 1933616 * 2 ^ 59
def prefixEnd_1933616 : Nat := 4983230072969 + 3 ^ 40 * 1933616 * 2
def baseEnd_1933616 : Nat := 661916272816141301471645

theorem tailTrace_1933616 : CollatzResearch.WordTrace tailWord_1933616 prefixEnd_1933616 661916272816141301471645 := by
  unfold tailWord_1933616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262384681423471083266351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47016512908564628111021801 35262384681423471083266351)
  ·
    refine ⟨52893577022135206624899527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35262384681423471083266351 52893577022135206624899527)
    ·
      refine ⟨79340365533202809937349291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52893577022135206624899527 79340365533202809937349291)
      ·
        refine ⟨119010548299804214906023937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79340365533202809937349291 119010548299804214906023937)
        ·
          refine ⟨89257911224853161179517953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119010548299804214906023937 89257911224853161179517953)
          ·
            refine ⟨66943433418639870884638465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89257911224853161179517953 66943433418639870884638465)
            ·
              refine ⟨50207575063979903163478849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66943433418639870884638465 50207575063979903163478849)
              ·
                refine ⟨37655681297984927372609137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50207575063979903163478849 37655681297984927372609137)
                ·
                  refine ⟨28241760973488695529456853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37655681297984927372609137 28241760973488695529456853)
                  ·
                    refine ⟨661916272816141301471645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28241760973488695529456853 661916272816141301471645)
                    ·
                      rfl

theorem cell22_1933616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_1933616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933616 prefixEnd_1933616 := by exact prefixLift 1933616
  have htrace : WordTrace (prefixWord ++ tailWord_1933616) baseStart_1933616 baseEnd_1933616 := by
    simpa [prefixWord, tailWord_1933616, baseEnd_1933616] using wordTrace_append hprefix tailTrace_1933616
  have hstable : (prefixWord ++ tailWord_1933616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933616).length < 2 ^ (prefixWord ++ tailWord_1933616).sum := by decide
  have hdescent : baseEnd_1933616 < baseStart_1933616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933663 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 5]
def baseStart_1933663 : Nat := 118140960795 + 1933663 * 2 ^ 59
def prefixEnd_1933663 : Nat := 4983230072969 + 3 ^ 40 * 1933663 * 2
def baseEnd_1933663 : Nat := 220644120625549615182167

theorem tailTrace_1933663 : CollatzResearch.WordTrace tailWord_1933663 prefixEnd_1933663 220644120625549615182167 := by
  unfold tailWord_1933663
  simp only [CollatzResearch.WordTrace]
  refine ⟨70526483593676669193493643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47017655729117779462329095 70526483593676669193493643)
  ·
    refine ⟨105789725390515003790240465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70526483593676669193493643 105789725390515003790240465)
    ·
      refine ⟨79342294042886252842680349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105789725390515003790240465 79342294042886252842680349)
      ·
        refine ⟨29753360266082344816005131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79342294042886252842680349 29753360266082344816005131)
        ·
          refine ⟨44630040399123517224007697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29753360266082344816005131 44630040399123517224007697)
          ·
            refine ⟨33472530299342637918005773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44630040399123517224007697 33472530299342637918005773)
            ·
              refine ⟨12552198862253489219252165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33472530299342637918005773 12552198862253489219252165)
              ·
                refine ⟨2353537286672529228609781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12552198862253489219252165 2353537286672529228609781)
                ·
                  refine ⟨220644120625549615182167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353537286672529228609781 220644120625549615182167)
                  ·
                    rfl

theorem cell22_1933663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 5].length) (baseStart_1933663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933663 prefixEnd_1933663 := by exact prefixLift 1933663
  have htrace : WordTrace (prefixWord ++ tailWord_1933663) baseStart_1933663 baseEnd_1933663 := by
    simpa [prefixWord, tailWord_1933663, baseEnd_1933663] using wordTrace_append hprefix tailTrace_1933663
  have hstable : (prefixWord ++ tailWord_1933663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933663).length < 2 ^ (prefixWord ++ tailWord_1933663).sum := by decide
  have hdescent : baseEnd_1933663 < baseStart_1933663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933667 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 1, 3]
def baseStart_1933667 : Nat := 118140960795 + 1933667 * 2 ^ 59
def prefixEnd_1933667 : Nat := 4983230072969 + 3 ^ 40 * 1933667 * 2
def baseEnd_1933667 : Nat := 661933731158394168446489

theorem tailTrace_1933667 : CollatzResearch.WordTrace tailWord_1933667 prefixEnd_1933667 661933731158394168446489 := by
  unfold tailWord_1933667
  simp only [CollatzResearch.WordTrace]
  refine ⟨70526629485662177876639255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47017752990441451917759503 70526629485662177876639255)
  ·
    refine ⟨105789944228493266814958883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70526629485662177876639255 105789944228493266814958883)
    ·
      refine ⟨158684916342739900222438325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105789944228493266814958883 158684916342739900222438325)
      ·
        refine ⟨14876710907131865645853593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158684916342739900222438325 14876710907131865645853593)
        ·
          refine ⟨11157533180348899234390195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14876710907131865645853593 11157533180348899234390195)
          ·
            refine ⟨16736299770523348851585293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11157533180348899234390195 16736299770523348851585293)
            ·
              refine ⟨6276112413946255819344485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16736299770523348851585293 6276112413946255819344485)
              ·
                refine ⟨1176771077614922966127091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6276112413946255819344485 1176771077614922966127091)
                ·
                  refine ⟨1765156616422384449190637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176771077614922966127091 1765156616422384449190637)
                  ·
                    refine ⟨661933731158394168446489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765156616422384449190637 661933731158394168446489)
                    ·
                      rfl

theorem cell22_1933667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 3].length) (baseStart_1933667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933667 prefixEnd_1933667 := by exact prefixLift 1933667
  have htrace : WordTrace (prefixWord ++ tailWord_1933667) baseStart_1933667 baseEnd_1933667 := by
    simpa [prefixWord, tailWord_1933667, baseEnd_1933667] using wordTrace_append hprefix tailTrace_1933667
  have hstable : (prefixWord ++ tailWord_1933667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933667).length < 2 ^ (prefixWord ++ tailWord_1933667).sum := by decide
  have hdescent : baseEnd_1933667 < baseStart_1933667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933718 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1933718 : Nat := 118140960795 + 1933718 * 2 ^ 59
def prefixEnd_1933718 : Nat := 4983230072969 + 3 ^ 40 * 1933718 * 2
def baseEnd_1933718 : Nat := 661951189500647035421333

theorem tailTrace_1933718 : CollatzResearch.WordTrace tailWord_1933718 prefixEnd_1933718 661951189500647035421333 := by
  unfold tailWord_1933718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408030600529838349171613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47018993072318275724497205 4408030600529838349171613)
  ·
    refine ⟨1653011475198689380939355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4408030600529838349171613 1653011475198689380939355)
    ·
      refine ⟨2479517212798034071409033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653011475198689380939355 2479517212798034071409033)
      ·
        refine ⟨1859637909598525553556775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479517212798034071409033 1859637909598525553556775)
        ·
          refine ⟨2789456864397788330335163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859637909598525553556775 2789456864397788330335163)
          ·
            refine ⟨4184185296596682495502745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789456864397788330335163 4184185296596682495502745)
            ·
              refine ⟨3138138972447511871627059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4184185296596682495502745 3138138972447511871627059)
              ·
                refine ⟨4707208458671267807440589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138138972447511871627059 4707208458671267807440589)
                ·
                  refine ⟨1765203172001725427790221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4707208458671267807440589 1765203172001725427790221)
                  ·
                    refine ⟨661951189500647035421333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765203172001725427790221 661951189500647035421333)
                    ·
                      rfl

theorem cell22_1933718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1933718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933718 prefixEnd_1933718 := by exact prefixLift 1933718
  have htrace : WordTrace (prefixWord ++ tailWord_1933718) baseStart_1933718 baseEnd_1933718 := by
    simpa [prefixWord, tailWord_1933718, baseEnd_1933718] using wordTrace_append hprefix tailTrace_1933718
  have hstable : (prefixWord ++ tailWord_1933718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933718).length < 2 ^ (prefixWord ++ tailWord_1933718).sum := by decide
  have hdescent : baseEnd_1933718 < baseStart_1933718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933772 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_1933772 : Nat := 118140960795 + 1933772 * 2 ^ 59
def prefixEnd_1933772 : Nat := 4983230072969 + 3 ^ 40 * 1933772 * 2
def baseEnd_1933772 : Nat := 661969674804208894571167

theorem tailTrace_1933772 : CollatzResearch.WordTrace tailWord_1933772 prefixEnd_1933772 661969674804208894571167 := by
  unfold tailWord_1933772
  simp only [CollatzResearch.WordTrace]
  refine ⟨35265229575140890404605785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47020306100187853872807713 35265229575140890404605785)
  ·
    refine ⟨26448922181355667803454339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35265229575140890404605785 26448922181355667803454339)
    ·
      refine ⟨39673383272033501705181509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26448922181355667803454339 39673383272033501705181509)
      ·
        refine ⟨7438759363506281569721533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39673383272033501705181509 7438759363506281569721533)
        ·
          refine ⟨2789534761314855588645575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7438759363506281569721533 2789534761314855588645575)
          ·
            refine ⟨4184302141972283382968363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789534761314855588645575 4184302141972283382968363)
            ·
              refine ⟨6276453212958425074452545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184302141972283382968363 6276453212958425074452545)
              ·
                refine ⟨4707339909718818805839409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6276453212958425074452545 4707339909718818805839409)
                ·
                  refine ⟨3530504932289114104379557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4707339909718818805839409 3530504932289114104379557)
                  ·
                    refine ⟨661969674804208894571167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530504932289114104379557 661969674804208894571167)
                    ·
                      rfl

theorem cell22_1933772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_1933772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933772 prefixEnd_1933772 := by exact prefixLift 1933772
  have htrace : WordTrace (prefixWord ++ tailWord_1933772) baseStart_1933772 baseEnd_1933772 := by
    simpa [prefixWord, tailWord_1933772, baseEnd_1933772] using wordTrace_append hprefix tailTrace_1933772
  have hstable : (prefixWord ++ tailWord_1933772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933772).length < 2 ^ (prefixWord ++ tailWord_1933772).sum := by decide
  have hdescent : baseEnd_1933772 < baseStart_1933772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933836 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_1933836 : Nat := 118140960795 + 1933836 * 2 ^ 59
def prefixEnd_1933836 : Nat := 4983230072969 + 3 ^ 40 * 1933836 * 2
def baseEnd_1933836 : Nat := 661991583312134060970971

theorem tailTrace_1933836 : CollatzResearch.WordTrace tailWord_1933836 prefixEnd_1933836 661991583312134060970971 := by
  unfold tailWord_1933836
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266396711024959869770681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47021862281366613159694241 35266396711024959869770681)
  ·
    refine ⟨26449797533268719902328011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35266396711024959869770681 26449797533268719902328011)
    ·
      refine ⟨39674696299903079853492017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26449797533268719902328011 39674696299903079853492017)
      ·
        refine ⟨29756022224927309890119013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39674696299903079853492017 29756022224927309890119013)
        ·
          refine ⟨5579254167173870604397315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29756022224927309890119013 5579254167173870604397315)
          ·
            refine ⟨8368881250760805906595973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579254167173870604397315 8368881250760805906595973)
            ·
              refine ⟨1569165234517651107486745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8368881250760805906595973 1569165234517651107486745)
              ·
                refine ⟨1176873925888238330615059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569165234517651107486745 1176873925888238330615059)
                ·
                  refine ⟨1765310888832357495922589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176873925888238330615059 1765310888832357495922589)
                  ·
                    refine ⟨661991583312134060970971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765310888832357495922589 661991583312134060970971)
                    ·
                      rfl

theorem cell22_1933836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_1933836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933836 prefixEnd_1933836 := by exact prefixLift 1933836
  have htrace : WordTrace (prefixWord ++ tailWord_1933836) baseStart_1933836 baseEnd_1933836 := by
    simpa [prefixWord, tailWord_1933836, baseEnd_1933836] using wordTrace_append hprefix tailTrace_1933836
  have hstable : (prefixWord ++ tailWord_1933836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933836).length < 2 ^ (prefixWord ++ tailWord_1933836).sum := by decide
  have hdescent : baseEnd_1933836 < baseStart_1933836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933845 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1933845 : Nat := 118140960795 + 1933845 * 2 ^ 59
def prefixEnd_1933845 : Nat := 4983230072969 + 3 ^ 40 * 1933845 * 2
def baseEnd_1933845 : Nat := 661994664196061037495943

theorem tailTrace_1933845 : CollatzResearch.WordTrace tailWord_1933845 prefixEnd_1933845 661994664196061037495943 := by
  unfold tailWord_1933845
  simp only [CollatzResearch.WordTrace]
  refine ⟨70533121679017314276618989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47022081119344876184412659 70533121679017314276618989)
  ·
    refine ⟨26449920629631492853732121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70533121679017314276618989 26449920629631492853732121)
    ·
      refine ⟨19837440472223619640299091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26449920629631492853732121 19837440472223619640299091)
      ·
        refine ⟨29756160708335429460448637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19837440472223619640299091 29756160708335429460448637)
        ·
          refine ⟨11158560265625786047668239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29756160708335429460448637 11158560265625786047668239)
          ·
            refine ⟨16737840398438679071502359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11158560265625786047668239 16737840398438679071502359)
            ·
              refine ⟨25106760597658018607253539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16737840398438679071502359 25106760597658018607253539)
              ·
                refine ⟨37660140896487027910880309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25106760597658018607253539 37660140896487027910880309)
                ·
                  refine ⟨3530638209045658866645029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37660140896487027910880309 3530638209045658866645029)
                  ·
                    refine ⟨661994664196061037495943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530638209045658866645029 661994664196061037495943)
                    ·
                      rfl

theorem cell22_1933845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1933845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933845 prefixEnd_1933845 := by exact prefixLift 1933845
  have htrace : WordTrace (prefixWord ++ tailWord_1933845) baseStart_1933845 baseEnd_1933845 := by
    simpa [prefixWord, tailWord_1933845, baseEnd_1933845] using wordTrace_append hprefix tailTrace_1933845
  have hstable : (prefixWord ++ tailWord_1933845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933845).length < 2 ^ (prefixWord ++ tailWord_1933845).sum := by decide
  have hdescent : baseEnd_1933845 < baseStart_1933845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933875 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 1, 5]
def baseStart_1933875 : Nat := 118140960795 + 1933875 * 2 ^ 59
def prefixEnd_1933875 : Nat := 4983230072969 + 3 ^ 40 * 1933875 * 2
def baseEnd_1933875 : Nat := 662004933809150959245851

theorem tailTrace_1933875 : CollatzResearch.WordTrace tailWord_1933875 prefixEnd_1933875 662004933809150959245851 := by
  unfold tailWord_1933875
  simp only [CollatzResearch.WordTrace]
  refine ⟨70534215868908629400211079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47022810579272419600140719 70534215868908629400211079)
  ·
    refine ⟨105801323803362944100316619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70534215868908629400211079 105801323803362944100316619)
    ·
      refine ⟨158701985705044416150474929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105801323803362944100316619 158701985705044416150474929)
      ·
        refine ⟨119026489278783312112856197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158701985705044416150474929 119026489278783312112856197)
        ·
          refine ⟨22317466739771871021160537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119026489278783312112856197 22317466739771871021160537)
          ·
            refine ⟨16738100054828903265870403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22317466739771871021160537 16738100054828903265870403)
            ·
              refine ⟨25107150082243354898805605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16738100054828903265870403 25107150082243354898805605)
              ·
                refine ⟨4707590640420629043526051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25107150082243354898805605 4707590640420629043526051)
                ·
                  refine ⟨7061385960630943565289077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707590640420629043526051 7061385960630943565289077)
                  ·
                    refine ⟨662004933809150959245851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7061385960630943565289077 662004933809150959245851)
                    ·
                      rfl

theorem cell22_1933875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_1933875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933875 prefixEnd_1933875 := by exact prefixLift 1933875
  have htrace : WordTrace (prefixWord ++ tailWord_1933875) baseStart_1933875 baseEnd_1933875 := by
    simpa [prefixWord, tailWord_1933875, baseEnd_1933875] using wordTrace_append hprefix tailTrace_1933875
  have hstable : (prefixWord ++ tailWord_1933875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933875).length < 2 ^ (prefixWord ++ tailWord_1933875).sum := by decide
  have hdescent : baseEnd_1933875 < baseStart_1933875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933894 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1933894 : Nat := 118140960795 + 1933894 * 2 ^ 59
def prefixEnd_1933894 : Nat := 4983230072969 + 3 ^ 40 * 1933894 * 2
def baseEnd_1933894 : Nat := 220670479299147081006931

theorem tailTrace_1933894 : CollatzResearch.WordTrace tailWord_1933894 prefixEnd_1933894 220670479299147081006931 := by
  unfold tailWord_1933894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204215901744993613911023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47023272570559863763435157 2204215901744993613911023)
  ·
    refine ⟨3306323852617490420866535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2204215901744993613911023 3306323852617490420866535)
    ·
      refine ⟨4959485778926235631299803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3306323852617490420866535 4959485778926235631299803)
      ·
        refine ⟨7439228668389353446949705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959485778926235631299803 7439228668389353446949705)
        ·
          refine ⟨5579421501292015085212279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7439228668389353446949705 5579421501292015085212279)
          ·
            refine ⟨8369132251938022627818419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579421501292015085212279 8369132251938022627818419)
            ·
              refine ⟨12553698377907033941727629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369132251938022627818419 12553698377907033941727629)
              ·
                refine ⟨4707636891715137728147861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12553698377907033941727629 4707636891715137728147861)
                ·
                  refine ⟨220670479299147081006931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4707636891715137728147861 220670479299147081006931)
                  ·
                    rfl

theorem cell22_1933894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1933894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933894 prefixEnd_1933894 := by exact prefixLift 1933894
  have htrace : WordTrace (prefixWord ++ tailWord_1933894) baseStart_1933894 baseEnd_1933894 := by
    simpa [prefixWord, tailWord_1933894, baseEnd_1933894] using wordTrace_append hprefix tailTrace_1933894
  have hstable : (prefixWord ++ tailWord_1933894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933894).length < 2 ^ (prefixWord ++ tailWord_1933894).sum := by decide
  have hdescent : baseEnd_1933894 < baseStart_1933894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933928 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 4]
def baseStart_1933928 : Nat := 118140960795 + 1933928 * 2 ^ 59
def prefixEnd_1933928 : Nat := 4983230072969 + 3 ^ 40 * 1933928 * 2
def baseEnd_1933928 : Nat := 220674358930758829223563

theorem tailTrace_1933928 : CollatzResearch.WordTrace tailWord_1933928 prefixEnd_1933928 220674358930758829223563 := by
  unfold tailWord_1933928
  simp only [CollatzResearch.WordTrace]
  refine ⟨35268074468858309725945219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47024099291811079634593625 35268074468858309725945219)
  ·
    refine ⟨52902111703287464588917829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35268074468858309725945219 52902111703287464588917829)
    ·
      refine ⟨9919145944366399610422093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52902111703287464588917829 9919145944366399610422093)
      ·
        refine ⟨3719679729137399853908285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9919145944366399610422093 3719679729137399853908285)
        ·
          refine ⟨1394879898426524945215607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3719679729137399853908285 1394879898426524945215607)
          ·
            refine ⟨2092319847639787417823411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394879898426524945215607 2092319847639787417823411)
            ·
              refine ⟨3138479771459681126735117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092319847639787417823411 3138479771459681126735117)
              ·
                refine ⟨1176929914297380422525669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3138479771459681126735117 1176929914297380422525669)
                ·
                  refine ⟨220674358930758829223563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1176929914297380422525669 220674358930758829223563)
                  ·
                    rfl

theorem cell22_1933928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_1933928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1933928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1933928 prefixEnd_1933928 := by exact prefixLift 1933928
  have htrace : WordTrace (prefixWord ++ tailWord_1933928) baseStart_1933928 baseEnd_1933928 := by
    simpa [prefixWord, tailWord_1933928, baseEnd_1933928] using wordTrace_append hprefix tailTrace_1933928
  have hstable : (prefixWord ++ tailWord_1933928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933928).length < 2 ^ (prefixWord ++ tailWord_1933928).sum := by decide
  have hdescent : baseEnd_1933928 < baseStart_1933928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934001 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 5]
def baseStart_1934001 : Nat := 118140960795 + 1934001 * 2 ^ 59
def prefixEnd_1934001 : Nat := 4983230072969 + 3 ^ 40 * 1934001 * 2
def baseEnd_1934001 : Nat := 220682688728042876865155

theorem tailTrace_1934001 : CollatzResearch.WordTrace tailWord_1934001 prefixEnd_1934001 220682688728042876865155 := by
  unfold tailWord_1934001
  simp only [CollatzResearch.WordTrace]
  refine ⟨70538811466452152919297857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47025874310968101946198571 70538811466452152919297857)
  ·
    refine ⟨52904108599839114689473393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70538811466452152919297857 52904108599839114689473393)
    ·
      refine ⟨39678081449879336017105045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52904108599839114689473393 39678081449879336017105045)
      ·
        refine ⟨1859910067963093875801799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39678081449879336017105045 1859910067963093875801799)
        ·
          refine ⟨2789865101944640813702699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859910067963093875801799 2789865101944640813702699)
          ·
            refine ⟨4184797652916961220554049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789865101944640813702699 4184797652916961220554049)
            ·
              refine ⟨3138598239687720915415537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4184797652916961220554049 3138598239687720915415537)
              ·
                refine ⟨2353948679765790686561653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3138598239687720915415537 2353948679765790686561653)
                ·
                  refine ⟨220682688728042876865155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353948679765790686561653 220682688728042876865155)
                  ·
                    rfl

theorem cell22_1934001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_1934001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934001 prefixEnd_1934001 := by exact prefixLift 1934001
  have htrace : WordTrace (prefixWord ++ tailWord_1934001) baseStart_1934001 baseEnd_1934001 := by
    simpa [prefixWord, tailWord_1934001, baseEnd_1934001] using wordTrace_append hprefix tailTrace_1934001
  have hstable : (prefixWord ++ tailWord_1934001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934001).length < 2 ^ (prefixWord ++ tailWord_1934001).sum := by decide
  have hdescent : baseEnd_1934001 < baseStart_1934001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934005 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1934005 : Nat := 118140960795 + 1934005 * 2 ^ 59
def prefixEnd_1934005 : Nat := 4983230072969 + 3 ^ 40 * 1934005 * 2
def baseEnd_1934005 : Nat := 662049435465873953495453

theorem tailTrace_1934005 : CollatzResearch.WordTrace tailWord_1934005 prefixEnd_1934005 662049435465873953495453 := by
  unfold tailWord_1934005
  simp only [CollatzResearch.WordTrace]
  refine ⟨70538957358437661602443469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47025971572291774401628979 70538957358437661602443469)
  ·
    refine ⟨26452109009414123100916301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70538957358437661602443469 26452109009414123100916301)
    ·
      refine ⟨9919540878530296162843613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26452109009414123100916301 9919540878530296162843613)
      ·
        refine ⟨3719827829448861061066355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9919540878530296162843613 3719827829448861061066355)
        ·
          refine ⟨5579741744173291591599533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719827829448861061066355 5579741744173291591599533)
          ·
            refine ⟨2092403154064984346849825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5579741744173291591599533 2092403154064984346849825)
            ·
              refine ⟨1569302365548738260137369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092403154064984346849825 1569302365548738260137369)
              ·
                refine ⟨1176976774161553695103027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569302365548738260137369 1176976774161553695103027)
                ·
                  refine ⟨1765465161242330542654541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176976774161553695103027 1765465161242330542654541)
                  ·
                    refine ⟨662049435465873953495453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765465161242330542654541 662049435465873953495453)
                    ·
                      rfl

theorem cell22_1934005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1934005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934005 prefixEnd_1934005 := by exact prefixLift 1934005
  have htrace : WordTrace (prefixWord ++ tailWord_1934005) baseStart_1934005 baseEnd_1934005 := by
    simpa [prefixWord, tailWord_1934005, baseEnd_1934005] using wordTrace_append hprefix tailTrace_1934005
  have hstable : (prefixWord ++ tailWord_1934005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934005).length < 2 ^ (prefixWord ++ tailWord_1934005).sum := by decide
  have hdescent : baseEnd_1934005 < baseStart_1934005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934012 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_1934012 : Nat := 118140960795 + 1934012 * 2 ^ 59
def prefixEnd_1934012 : Nat := 4983230072969 + 3 ^ 40 * 1934012 * 2
def baseEnd_1934012 : Nat := 220683943902976089523477

theorem tailTrace_1934012 : CollatzResearch.WordTrace tailWord_1934012 prefixEnd_1934012 220683943902976089523477 := by
  unfold tailWord_1934012
  simp only [CollatzResearch.WordTrace]
  refine ⟨35269606334706150898974145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47026141779608201198632193 35269606334706150898974145)
  ·
    refine ⟨26452204751029613174230609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35269606334706150898974145 26452204751029613174230609)
    ·
      refine ⟨19839153563272209880672957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26452204751029613174230609 19839153563272209880672957)
      ·
        refine ⟨7439682586227078705252359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19839153563272209880672957 7439682586227078705252359)
        ·
          refine ⟨11159523879340618057878539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7439682586227078705252359 11159523879340618057878539)
          ·
            refine ⟨16739285819010927086817809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159523879340618057878539 16739285819010927086817809)
            ·
              refine ⟨12554464364258195315113357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16739285819010927086817809 12554464364258195315113357)
              ·
                refine ⟨4707924136596823243167509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12554464364258195315113357 4707924136596823243167509)
                ·
                  refine ⟨220683943902976089523477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4707924136596823243167509 220683943902976089523477)
                  ·
                    rfl

theorem cell22_1934012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_1934012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934012 prefixEnd_1934012 := by exact prefixLift 1934012
  have htrace : WordTrace (prefixWord ++ tailWord_1934012) baseStart_1934012 baseEnd_1934012 := by
    simpa [prefixWord, tailWord_1934012, baseEnd_1934012] using wordTrace_append hprefix tailTrace_1934012
  have hstable : (prefixWord ++ tailWord_1934012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934012).length < 2 ^ (prefixWord ++ tailWord_1934012).sum := by decide
  have hdescent : baseEnd_1934012 < baseStart_1934012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934027 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 8, 3]
def baseStart_1934027 : Nat := 118140960795 + 1934027 * 2 ^ 59
def prefixEnd_1934027 : Nat := 4983230072969 + 3 ^ 40 * 1934027 * 2
def baseEnd_1934027 : Nat := 662056966515473229445385

theorem tailTrace_1934027 : CollatzResearch.WordTrace tailWord_1934027 prefixEnd_1934027 662056966515473229445385 := by
  unfold tailWord_1934027
  simp only [CollatzResearch.WordTrace]
  refine ⟨70539759764357959359744335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47026506509571972906496223 70539759764357959359744335)
  ·
    refine ⟨105809639646536939039616503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70539759764357959359744335 105809639646536939039616503)
    ·
      refine ⟨158714459469805408559424755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105809639646536939039616503 158714459469805408559424755)
      ·
        refine ⟨238071689204708112839137133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158714459469805408559424755 238071689204708112839137133)
        ·
          refine ⟨89276883451765542314676425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238071689204708112839137133 89276883451765542314676425)
          ·
            refine ⟨66957662588824156736007319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89276883451765542314676425 66957662588824156736007319)
            ·
              refine ⟨100436493883236235104010979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66957662588824156736007319 100436493883236235104010979)
              ·
                refine ⟨150654740824854352656016469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100436493883236235104010979 150654740824854352656016469)
                ·
                  refine ⟨1765485244041261945187693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 150654740824854352656016469 1765485244041261945187693)
                  ·
                    refine ⟨662056966515473229445385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765485244041261945187693 662056966515473229445385)
                    ·
                      rfl

theorem cell22_1934027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 3].length) (baseStart_1934027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934027 prefixEnd_1934027 := by exact prefixLift 1934027
  have htrace : WordTrace (prefixWord ++ tailWord_1934027) baseStart_1934027 baseEnd_1934027 := by
    simpa [prefixWord, tailWord_1934027, baseEnd_1934027] using wordTrace_append hprefix tailTrace_1934027
  have hstable : (prefixWord ++ tailWord_1934027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934027).length < 2 ^ (prefixWord ++ tailWord_1934027).sum := by decide
  have hdescent : baseEnd_1934027 < baseStart_1934027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934042 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_1934042 : Nat := 118140960795 + 1934042 * 2 ^ 59
def prefixEnd_1934042 : Nat := 4983230072969 + 3 ^ 40 * 1934042 * 2
def baseEnd_1934042 : Nat := 662062101322018190320339

theorem tailTrace_1934042 : CollatzResearch.WordTrace tailWord_1934042 prefixEnd_1934042 662062101322018190320339 := by
  unfold tailWord_1934042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17635076714825904230385095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47026871239535744614360253 17635076714825904230385095)
  ·
    refine ⟨26452615072238856345577643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17635076714825904230385095 26452615072238856345577643)
    ·
      refine ⟨39678922608358284518366465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26452615072238856345577643 39678922608358284518366465)
      ·
        refine ⟨29759191956268713388774849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39678922608358284518366465 29759191956268713388774849)
        ·
          refine ⟨22319393967201535041581137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29759191956268713388774849 22319393967201535041581137)
          ·
            refine ⟨16739545475401151281185853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22319393967201535041581137 16739545475401151281185853)
            ·
              refine ⟨6277329553275431730444695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16739545475401151281185853 6277329553275431730444695)
              ·
                refine ⟨9415994329913147595667043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277329553275431730444695 9415994329913147595667043)
                ·
                  refine ⟨14123991494869721393500565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9415994329913147595667043 14123991494869721393500565)
                  ·
                    refine ⟨662062101322018190320339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14123991494869721393500565 662062101322018190320339)
                    ·
                      rfl

theorem cell22_1934042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_1934042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934042 prefixEnd_1934042 := by exact prefixLift 1934042
  have htrace : WordTrace (prefixWord ++ tailWord_1934042) baseStart_1934042 baseEnd_1934042 := by
    simpa [prefixWord, tailWord_1934042, baseEnd_1934042] using wordTrace_append hprefix tailTrace_1934042
  have hstable : (prefixWord ++ tailWord_1934042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934042).length < 2 ^ (prefixWord ++ tailWord_1934042).sum := by decide
  have hdescent : baseEnd_1934042 < baseStart_1934042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934089 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_1934089 : Nat := 118140960795 + 1934089 * 2 ^ 59
def prefixEnd_1934089 : Nat := 4983230072969 + 3 ^ 40 * 1934089 * 2
def baseEnd_1934089 : Nat := 662078190382525734395195

theorem tailTrace_1934089 : CollatzResearch.WordTrace tailWord_1934089 prefixEnd_1934089 662078190382525734395195 := by
  unfold tailWord_1934089
  simp only [CollatzResearch.WordTrace]
  refine ⟨70542021090133343948501321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47028014060088895965667547 70542021090133343948501321)
  ·
    refine ⟨52906515817600007961375991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70542021090133343948501321 52906515817600007961375991)
    ·
      refine ⟨79359773726400011942063987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52906515817600007961375991 79359773726400011942063987)
      ·
        refine ⟨119039660589600017913095981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79359773726400011942063987 119039660589600017913095981)
        ·
          refine ⟨44639872721100006717410993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119039660589600017913095981 44639872721100006717410993)
          ·
            refine ⟨33479904540825005038058245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44639872721100006717410993 33479904540825005038058245)
            ·
              refine ⟨6277482101404688444635921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33479904540825005038058245 6277482101404688444635921)
              ·
                refine ⟨4708111576053516333476941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277482101404688444635921 4708111576053516333476941)
                ·
                  refine ⟨1765541841020068625053853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4708111576053516333476941 1765541841020068625053853)
                  ·
                    refine ⟨662078190382525734395195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765541841020068625053853 662078190382525734395195)
                    ·
                      rfl

theorem cell22_1934089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_1934089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934089 prefixEnd_1934089 := by exact prefixLift 1934089
  have htrace : WordTrace (prefixWord ++ tailWord_1934089) baseStart_1934089 baseEnd_1934089 := by
    simpa [prefixWord, tailWord_1934089, baseEnd_1934089] using wordTrace_append hprefix tailTrace_1934089
  have hstable : (prefixWord ++ tailWord_1934089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934089).length < 2 ^ (prefixWord ++ tailWord_1934089).sum := by decide
  have hdescent : baseEnd_1934089 < baseStart_1934089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934147 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 8]
def baseStart_1934147 : Nat := 118140960795 + 1934147 * 2 ^ 59
def prefixEnd_1934147 : Nat := 4983230072969 + 3 ^ 40 * 1934147 * 2
def baseEnd_1934147 : Nat := 220699348322610972148339

theorem tailTrace_1934147 : CollatzResearch.WordTrace tailWord_1934147 prefixEnd_1934147 220699348322610972148339 := by
  unfold tailWord_1934147
  simp only [CollatzResearch.WordTrace]
  refine ⟨70544136523923219854112695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47029424349282146569408463 70544136523923219854112695)
  ·
    refine ⟨105816204785884829781169043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70544136523923219854112695 105816204785884829781169043)
    ·
      refine ⟨158724307178827244671753565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105816204785884829781169043 158724307178827244671753565)
      ·
        refine ⟨59521615192060216751907587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158724307178827244671753565 59521615192060216751907587)
        ·
          refine ⟨89282422788090325127861381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59521615192060216751907587 89282422788090325127861381)
          ·
            refine ⟨16740454272766935961474009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89282422788090325127861381 16740454272766935961474009)
            ·
              refine ⟨12555340704575201971105507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16740454272766935961474009 12555340704575201971105507)
              ·
                refine ⟨18833011056862802956658261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555340704575201971105507 18833011056862802956658261)
                ·
                  refine ⟨220699348322610972148339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18833011056862802956658261 220699348322610972148339)
                  ·
                    rfl

theorem cell22_1934147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_1934147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934147 prefixEnd_1934147 := by exact prefixLift 1934147
  have htrace : WordTrace (prefixWord ++ tailWord_1934147) baseStart_1934147 baseEnd_1934147 := by
    simpa [prefixWord, tailWord_1934147, baseEnd_1934147] using wordTrace_append hprefix tailTrace_1934147
  have hstable : (prefixWord ++ tailWord_1934147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934147).length < 2 ^ (prefixWord ++ tailWord_1934147).sum := by decide
  have hdescent : baseEnd_1934147 < baseStart_1934147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934149 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_1934149 : Nat := 118140960795 + 1934149 * 2 ^ 59
def prefixEnd_1934149 : Nat := 4983230072969 + 3 ^ 40 * 1934149 * 2
def baseEnd_1934149 : Nat := 662098729608705577895011

theorem tailTrace_1934149 : CollatzResearch.WordTrace tailWord_1934149 prefixEnd_1934149 662098729608705577895011 := by
  unfold tailWord_1934149
  simp only [CollatzResearch.WordTrace]
  refine ⟨70544209469915974195685501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47029472979943982797123667 70544209469915974195685501)
  ·
    refine ⟨26454078551218490323382063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70544209469915974195685501 26454078551218490323382063)
    ·
      refine ⟨39681117826827735485073095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26454078551218490323382063 39681117826827735485073095)
      ·
        refine ⟨59521676740241603227609643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39681117826827735485073095 59521676740241603227609643)
        ·
          refine ⟨89282515110362404841414465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59521676740241603227609643 89282515110362404841414465)
          ·
            refine ⟨66961886332771803631060849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89282515110362404841414465 66961886332771803631060849)
            ·
              refine ⟨50221414749578852723295637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66961886332771803631060849 50221414749578852723295637)
              ·
                refine ⟨2354128816386508721404483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50221414749578852723295637 2354128816386508721404483)
                ·
                  refine ⟨3531193224579763082106725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354128816386508721404483 3531193224579763082106725)
                  ·
                    refine ⟨662098729608705577895011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531193224579763082106725 662098729608705577895011)
                    ·
                      rfl

theorem cell22_1934149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_1934149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934149 prefixEnd_1934149 := by exact prefixLift 1934149
  have htrace : WordTrace (prefixWord ++ tailWord_1934149) baseStart_1934149 baseEnd_1934149 := by
    simpa [prefixWord, tailWord_1934149, baseEnd_1934149] using wordTrace_append hprefix tailTrace_1934149
  have hstable : (prefixWord ++ tailWord_1934149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934149).length < 2 ^ (prefixWord ++ tailWord_1934149).sum := by decide
  have hdescent : baseEnd_1934149 < baseStart_1934149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934194 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1934194 : Nat := 118140960795 + 1934194 * 2 ^ 59
def prefixEnd_1934194 : Nat := 4983230072969 + 3 ^ 40 * 1934194 * 2
def baseEnd_1934194 : Nat := 662114134028340460519873

theorem tailTrace_1934194 : CollatzResearch.WordTrace tailWord_1934194 prefixEnd_1934194 662114134028340460519873 := by
  unfold tailWord_1934194
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636462688688236720268409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47030567169835297920715757 17636462688688236720268409)
  ·
    refine ⟨13227347016516177540201307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17636462688688236720268409 13227347016516177540201307)
    ·
      refine ⟨19841020524774266310301961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13227347016516177540201307 19841020524774266310301961)
      ·
        refine ⟨14880765393580699732726471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19841020524774266310301961 14880765393580699732726471)
        ·
          refine ⟨22321148090371049599089707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14880765393580699732726471 22321148090371049599089707)
          ·
            refine ⟨33481722135556574398634561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22321148090371049599089707 33481722135556574398634561)
            ·
              refine ⟨25111291601667430798975921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33481722135556574398634561 25111291601667430798975921)
              ·
                refine ⟨18833468701250573099231941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25111291601667430798975921 18833468701250573099231941)
                ·
                  refine ⟨3531275381484482456105989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18833468701250573099231941 3531275381484482456105989)
                  ·
                    refine ⟨662114134028340460519873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531275381484482456105989 662114134028340460519873)
                    ·
                      rfl

theorem cell22_1934194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1934194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934194 prefixEnd_1934194 := by exact prefixLift 1934194
  have htrace : WordTrace (prefixWord ++ tailWord_1934194) baseStart_1934194 baseEnd_1934194 := by
    simpa [prefixWord, tailWord_1934194, baseEnd_1934194] using wordTrace_append hprefix tailTrace_1934194
  have hstable : (prefixWord ++ tailWord_1934194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934194).length < 2 ^ (prefixWord ++ tailWord_1934194).sum := by decide
  have hdescent : baseEnd_1934194 < baseStart_1934194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934226 : List Nat := [3, 2, 3, 2, 2, 1, 9]
def baseStart_1934226 : Nat := 118140960795 + 1934226 * 2 ^ 59
def prefixEnd_1934226 : Nat := 4983230072969 + 3 ^ 40 * 1934226 * 2
def baseEnd_1934226 : Nat := 24523151417863075693325

theorem tailTrace_1934226 : CollatzResearch.WordTrace tailWord_1934226 prefixEnd_1934226 24523151417863075693325 := by
  unfold tailWord_1934226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636754472659254086559633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47031345260424677564159021 17636754472659254086559633)
  ·
    refine ⟨13227565854494440564919725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17636754472659254086559633 13227565854494440564919725)
    ·
      refine ⟨4960337195435415211844897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13227565854494440564919725 4960337195435415211844897)
      ·
        refine ⟨3720252896576561408883673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4960337195435415211844897 3720252896576561408883673)
        ·
          refine ⟨2790189672432421056662755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3720252896576561408883673 2790189672432421056662755)
          ·
            refine ⟨4185284508648631584994133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790189672432421056662755 4185284508648631584994133)
            ·
              refine ⟨24523151417863075693325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4185284508648631584994133 24523151417863075693325)
              ·
                rfl

theorem cell22_1934226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 9].length) (baseStart_1934226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934226 prefixEnd_1934226 := by exact prefixLift 1934226
  have htrace : WordTrace (prefixWord ++ tailWord_1934226) baseStart_1934226 baseEnd_1934226 := by
    simpa [prefixWord, tailWord_1934226, baseEnd_1934226] using wordTrace_append hprefix tailTrace_1934226
  have hstable : (prefixWord ++ tailWord_1934226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934226).length < 2 ^ (prefixWord ++ tailWord_1934226).sum := by decide
  have hdescent : baseEnd_1934226 < baseStart_1934226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934260 : List Nat := [2, 5, 2, 1, 1, 3, 2, 6]
def baseStart_1934260 : Nat := 118140960795 + 1934260 * 2 ^ 59
def prefixEnd_1934260 : Nat := 4983230072969 + 3 ^ 40 * 1934260 * 2
def baseEnd_1934260 : Nat := 73570747464126476485519

theorem tailTrace_1934260 : CollatzResearch.WordTrace tailWord_1934260 prefixEnd_1934260 73570747464126476485519 := by
  unfold tailWord_1934260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274128986256920076488117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47032171981675893435317489 35274128986256920076488117)
  ·
    refine ⟨3306949592461586257170761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35274128986256920076488117 3306949592461586257170761)
    ·
      refine ⟨2480212194346189692878071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3306949592461586257170761 2480212194346189692878071)
      ·
        refine ⟨3720318291519284539317107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480212194346189692878071 3720318291519284539317107)
        ·
          refine ⟨5580477437278926808975661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720318291519284539317107 5580477437278926808975661)
          ·
            refine ⟨2092679038979597553365873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5580477437278926808975661 2092679038979597553365873)
            ·
              refine ⟨1569509279234698165024405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092679038979597553365873 1569509279234698165024405)
              ·
                refine ⟨73570747464126476485519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1569509279234698165024405 73570747464126476485519)
                ·
                  rfl

theorem cell22_1934260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 6].length) (baseStart_1934260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934260 prefixEnd_1934260 := by exact prefixLift 1934260
  have htrace : WordTrace (prefixWord ++ tailWord_1934260) baseStart_1934260 baseEnd_1934260 := by
    simpa [prefixWord, tailWord_1934260, baseEnd_1934260] using wordTrace_append hprefix tailTrace_1934260
  have hstable : (prefixWord ++ tailWord_1934260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934260).length < 2 ^ (prefixWord ++ tailWord_1934260).sum := by decide
  have hdescent : baseEnd_1934260 < baseStart_1934260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934292 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_1934292 : Nat := 118140960795 + 1934292 * 2 ^ 59
def prefixEnd_1934292 : Nat := 4983230072969 + 3 ^ 40 * 1934292 * 2
def baseEnd_1934292 : Nat := 662147681431100871569573

theorem tailTrace_1934292 : CollatzResearch.WordTrace tailWord_1934292 prefixEnd_1934292 662147681431100871569573 := by
  unfold tailWord_1934292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274712554198954809070565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47032950072265273078760753 35274712554198954809070565)
  ·
    refine ⟨6614008603912304026700731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35274712554198954809070565 6614008603912304026700731)
    ·
      refine ⟨9921012905868456040051097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6614008603912304026700731 9921012905868456040051097)
      ·
        refine ⟨7440759679401342030038323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9921012905868456040051097 7440759679401342030038323)
        ·
          refine ⟨11161139519102013045057485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440759679401342030038323 11161139519102013045057485)
          ·
            refine ⟨4185427319663254891896557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11161139519102013045057485 4185427319663254891896557)
            ·
              refine ⟨1569535244873720584461209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4185427319663254891896557 1569535244873720584461209)
              ·
                refine ⟨1177151433655290438345907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569535244873720584461209 1177151433655290438345907)
                ·
                  refine ⟨1765727150482935657518861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177151433655290438345907 1765727150482935657518861)
                  ·
                    refine ⟨662147681431100871569573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765727150482935657518861 662147681431100871569573)
                    ·
                      rfl

theorem cell22_1934292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_1934292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934292 prefixEnd_1934292 := by exact prefixLift 1934292
  have htrace : WordTrace (prefixWord ++ tailWord_1934292) baseStart_1934292 baseEnd_1934292 := by
    simpa [prefixWord, tailWord_1934292, baseEnd_1934292] using wordTrace_append hprefix tailTrace_1934292
  have hstable : (prefixWord ++ tailWord_1934292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934292).length < 2 ^ (prefixWord ++ tailWord_1934292).sum := by decide
  have hdescent : baseEnd_1934292 < baseStart_1934292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934318 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1934318 : Nat := 118140960795 + 1934318 * 2 ^ 59
def prefixEnd_1934318 : Nat := 4983230072969 + 3 ^ 40 * 1934318 * 2
def baseEnd_1934318 : Nat := 662156581762445470419493

theorem tailTrace_1934318 : CollatzResearch.WordTrace tailWord_1934318 prefixEnd_1934318 662156581762445470419493 := by
  unfold tailWord_1934318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818796675787964507323451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47033582270869144039058405 8818796675787964507323451)
  ·
    refine ⟨13228195013681946760985177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8818796675787964507323451 13228195013681946760985177)
    ·
      refine ⟨9921146260261460070738883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13228195013681946760985177 9921146260261460070738883)
      ·
        refine ⟨14881719390392190106108325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9921146260261460070738883 14881719390392190106108325)
        ·
          refine ⟨2790322385698535644895311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14881719390392190106108325 2790322385698535644895311)
          ·
            refine ⟨4185483578547803467342967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790322385698535644895311 4185483578547803467342967)
            ·
              refine ⟨6278225367821705201014451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185483578547803467342967 6278225367821705201014451)
              ·
                refine ⟨9417338051732557801521677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278225367821705201014451 9417338051732557801521677)
                ·
                  refine ⟨3531501769399709175570629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9417338051732557801521677 3531501769399709175570629)
                  ·
                    refine ⟨662156581762445470419493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531501769399709175570629 662156581762445470419493)
                    ·
                      rfl

theorem cell22_1934318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1934318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934318 prefixEnd_1934318 := by exact prefixLift 1934318
  have htrace : WordTrace (prefixWord ++ tailWord_1934318) baseStart_1934318 baseEnd_1934318 := by
    simpa [prefixWord, tailWord_1934318, baseEnd_1934318] using wordTrace_append hprefix tailTrace_1934318
  have hstable : (prefixWord ++ tailWord_1934318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934318).length < 2 ^ (prefixWord ++ tailWord_1934318).sum := by decide
  have hdescent : baseEnd_1934318 < baseStart_1934318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934344 : List Nat := [2, 1, 3, 2, 1, 13]
def baseStart_1934344 : Nat := 118140960795 + 1934344 * 2 ^ 59
def prefixEnd_1934344 : Nat := 4983230072969 + 3 ^ 40 * 1934344 * 2
def baseEnd_1934344 : Nat := 8174882494985062583573

theorem tailTrace_1934344 : CollatzResearch.WordTrace tailWord_1934344 prefixEnd_1934344 8174882494985062583573 := by
  unfold tailWord_1934344
  simp only [CollatzResearch.WordTrace]
  refine ⟨35275660852104761249517043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47034214469473014999356057 35275660852104761249517043)
  ·
    refine ⟨52913491278157141874275565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35275660852104761249517043 52913491278157141874275565)
    ·
      refine ⟨19842559229308928202853337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52913491278157141874275565 19842559229308928202853337)
      ·
        refine ⟨14881919421981696152140003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19842559229308928202853337 14881919421981696152140003)
        ·
          refine ⟨22322879132972544228210005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14881919421981696152140003 22322879132972544228210005)
          ·
            refine ⟨8174882494985062583573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 22322879132972544228210005 8174882494985062583573)
            ·
              rfl

theorem cell22_1934344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 13].length) (baseStart_1934344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934344 prefixEnd_1934344 := by exact prefixLift 1934344
  have htrace : WordTrace (prefixWord ++ tailWord_1934344) baseStart_1934344 baseEnd_1934344 := by
    simpa [prefixWord, tailWord_1934344, baseEnd_1934344] using wordTrace_append hprefix tailTrace_1934344
  have hstable : (prefixWord ++ tailWord_1934344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934344).length < 2 ^ (prefixWord ++ tailWord_1934344).sum := by decide
  have hdescent : baseEnd_1934344 < baseStart_1934344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934348 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_1934348 : Nat := 118140960795 + 1934348 * 2 ^ 59
def prefixEnd_1934348 : Nat := 4983230072969 + 3 ^ 40 * 1934348 * 2
def baseEnd_1934348 : Nat := 662166851375535392169401

theorem tailTrace_1934348 : CollatzResearch.WordTrace tailWord_1934348 prefixEnd_1934348 662166851375535392169401 := by
  unfold tailWord_1934348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35275733798097515591089849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47034311730796687454786465 35275733798097515591089849)
  ·
    refine ⟨26456800348573136693317387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35275733798097515591089849 26456800348573136693317387)
    ·
      refine ⟨39685200522859705039976081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26456800348573136693317387 39685200522859705039976081)
      ·
        refine ⟨29763900392144778779982061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39685200522859705039976081 29763900392144778779982061)
        ·
          refine ⟨11161462647054292042493273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29763900392144778779982061 11161462647054292042493273)
          ·
            refine ⟨8371096985290719031869955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11161462647054292042493273 8371096985290719031869955)
            ·
              refine ⟨12556645477936078547804933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371096985290719031869955 12556645477936078547804933)
              ·
                refine ⟨2354371027113014727713425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12556645477936078547804933 2354371027113014727713425)
                ·
                  refine ⟨1765778270334761045785069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354371027113014727713425 1765778270334761045785069)
                  ·
                    refine ⟨662166851375535392169401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765778270334761045785069 662166851375535392169401)
                    ·
                      rfl

theorem cell22_1934348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_1934348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934348 prefixEnd_1934348 := by exact prefixLift 1934348
  have htrace : WordTrace (prefixWord ++ tailWord_1934348) baseStart_1934348 baseEnd_1934348 := by
    simpa [prefixWord, tailWord_1934348, baseEnd_1934348] using wordTrace_append hprefix tailTrace_1934348
  have hstable : (prefixWord ++ tailWord_1934348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934348).length < 2 ^ (prefixWord ++ tailWord_1934348).sum := by decide
  have hdescent : baseEnd_1934348 < baseStart_1934348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934350 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1934350 : Nat := 118140960795 + 1934350 * 2 ^ 59
def prefixEnd_1934350 : Nat := 4983230072969 + 3 ^ 40 * 1934350 * 2
def baseEnd_1934350 : Nat := 220722512005469351206465

theorem tailTrace_1934350 : CollatzResearch.WordTrace tailWord_1934350 prefixEnd_1934350 220722512005469351206465 := by
  unfold tailWord_1934350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818942567773473190469063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47034360361458523682501669 8818942567773473190469063)
  ·
    refine ⟨13228413851660209785703595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8818942567773473190469063 13228413851660209785703595)
    ·
      refine ⟨19842620777490314678555393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13228413851660209785703595 19842620777490314678555393)
      ·
        refine ⟨14881965583117736008916545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19842620777490314678555393 14881965583117736008916545)
        ·
          refine ⟨11161474187338302006687409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881965583117736008916545 11161474187338302006687409)
          ·
            refine ⟨8371105640503726505015557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11161474187338302006687409 8371105640503726505015557)
            ·
              refine ⟨1569582307594448719690417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8371105640503726505015557 1569582307594448719690417)
              ·
                refine ⟨1177186730695836539767813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569582307594448719690417 1177186730695836539767813)
                ·
                  refine ⟨220722512005469351206465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177186730695836539767813 220722512005469351206465)
                  ·
                    rfl

theorem cell22_1934350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1934350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934350 prefixEnd_1934350 := by exact prefixLift 1934350
  have htrace : WordTrace (prefixWord ++ tailWord_1934350) baseStart_1934350 baseEnd_1934350 := by
    simpa [prefixWord, tailWord_1934350, baseEnd_1934350] using wordTrace_append hprefix tailTrace_1934350
  have hstable : (prefixWord ++ tailWord_1934350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934350).length < 2 ^ (prefixWord ++ tailWord_1934350).sum := by decide
  have hdescent : baseEnd_1934350 < baseStart_1934350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934410 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_1934410 : Nat := 118140960795 + 1934410 * 2 ^ 59
def prefixEnd_1934410 : Nat := 4983230072969 + 3 ^ 40 * 1934410 * 2
def baseEnd_1934410 : Nat := 662188075242587897119211

theorem tailTrace_1934410 : CollatzResearch.WordTrace tailWord_1934410 prefixEnd_1934410 662188075242587897119211 := by
  unfold tailWord_1934410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638432230492603942734171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47035819281313610513957789 17638432230492603942734171)
  ·
    refine ⟨26457648345738905914101257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17638432230492603942734171 26457648345738905914101257)
    ·
      refine ⟨19843236259304179435575943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26457648345738905914101257 19843236259304179435575943)
      ·
        refine ⟨29764854388956269153363915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19843236259304179435575943 29764854388956269153363915)
        ·
          refine ⟨44647281583434403730045873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29764854388956269153363915 44647281583434403730045873)
          ·
            refine ⟨33485461187575802797534405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44647281583434403730045873 33485461187575802797534405)
            ·
              refine ⟨6278523972670463024537701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33485461187575802797534405 6278523972670463024537701)
              ·
                refine ⟨1177223244875711817100819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6278523972670463024537701 1177223244875711817100819)
                ·
                  refine ⟨1765834867313567725651229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177223244875711817100819 1765834867313567725651229)
                  ·
                    refine ⟨662188075242587897119211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765834867313567725651229 662188075242587897119211)
                    ·
                      rfl

theorem cell22_1934410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_1934410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934410 prefixEnd_1934410 := by exact prefixLift 1934410
  have htrace : WordTrace (prefixWord ++ tailWord_1934410) baseStart_1934410 baseEnd_1934410 := by
    simpa [prefixWord, tailWord_1934410, baseEnd_1934410] using wordTrace_append hprefix tailTrace_1934410
  have hstable : (prefixWord ++ tailWord_1934410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934410).length < 2 ^ (prefixWord ++ tailWord_1934410).sum := by decide
  have hdescent : baseEnd_1934410 < baseStart_1934410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934421 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1934421 : Nat := 118140960795 + 1934421 * 2 ^ 59
def prefixEnd_1934421 : Nat := 4983230072969 + 3 ^ 40 * 1934421 * 2
def baseEnd_1934421 : Nat := 662191840767387535094177

theorem tailTrace_1934421 : CollatzResearch.WordTrace tailWord_1934421 prefixEnd_1934421 662191840767387535094177 := by
  unfold tailWord_1934421
  simp only [CollatzResearch.WordTrace]
  refine ⟨70554130124930564649587117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47036086749953709766391411 70554130124930564649587117)
  ·
    refine ⟨26457798796848961743595169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70554130124930564649587117 26457798796848961743595169)
    ·
      refine ⟨19843349097636721307696377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26457798796848961743595169 19843349097636721307696377)
      ·
        refine ⟨14882511823227540980772283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19843349097636721307696377 14882511823227540980772283)
        ·
          refine ⟨22323767734841311471158425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14882511823227540980772283 22323767734841311471158425)
          ·
            refine ⟨16742825801130983603368819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22323767734841311471158425 16742825801130983603368819)
            ·
              refine ⟨25114238701696475405053229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16742825801130983603368819 25114238701696475405053229)
              ·
                refine ⟨9417839513136178276894961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25114238701696475405053229 9417839513136178276894961)
                ·
                  refine ⟨7063379634852133707671221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9417839513136178276894961 7063379634852133707671221)
                  ·
                    refine ⟨662191840767387535094177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7063379634852133707671221 662191840767387535094177)
                    ·
                      rfl

theorem cell22_1934421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1934421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934421 prefixEnd_1934421 := by exact prefixLift 1934421
  have htrace : WordTrace (prefixWord ++ tailWord_1934421) baseStart_1934421 baseEnd_1934421 := by
    simpa [prefixWord, tailWord_1934421, baseEnd_1934421] using wordTrace_append hprefix tailTrace_1934421
  have hstable : (prefixWord ++ tailWord_1934421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934421).length < 2 ^ (prefixWord ++ tailWord_1934421).sum := by decide
  have hdescent : baseEnd_1934421 < baseStart_1934421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
