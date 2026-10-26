import V185TrunkScan22Chunk267

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2389590 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2389590 : Nat := 118140960795 + 2389590 * 2 ^ 59
def prefixEnd_2389590 : Nat := 4983230072969 + 3 ^ 40 * 2389590 * 2
def baseEnd_2389590 : Nat := 818005491451607301223655

theorem tailTrace_2389590 : CollatzResearch.WordTrace tailWord_2389590 prefixEnd_2389590 818005491451607301223655 := by
  unfold tailWord_2389590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5447219213308188395365889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58103671608620676217236149 5447219213308188395365889)
  ·
    refine ⟨4085414409981141296524417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5447219213308188395365889 4085414409981141296524417)
    ·
      refine ⟨3064060807485855972393313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4085414409981141296524417 3064060807485855972393313)
      ·
        refine ⟨2298045605614391979294985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3064060807485855972393313 2298045605614391979294985)
        ·
          refine ⟨1723534204210793984471239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298045605614391979294985 1723534204210793984471239)
          ·
            refine ⟨2585301306316190976706859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723534204210793984471239 2585301306316190976706859)
            ·
              refine ⟨3877951959474286465060289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585301306316190976706859 3877951959474286465060289)
              ·
                refine ⟨2908463969605714848795217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877951959474286465060289 2908463969605714848795217)
                ·
                  refine ⟨2181347977204286136596413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2908463969605714848795217 2181347977204286136596413)
                  ·
                    refine ⟨818005491451607301223655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181347977204286136596413 818005491451607301223655)
                    ·
                      rfl

theorem cell22_2389590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2389590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389590 prefixEnd_2389590 := by exact prefixLift 2389590
  have htrace : WordTrace (prefixWord ++ tailWord_2389590) baseStart_2389590 baseEnd_2389590 := by
    simpa [prefixWord, tailWord_2389590, baseEnd_2389590] using wordTrace_append hprefix tailTrace_2389590
  have hstable : (prefixWord ++ tailWord_2389590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389590).length < 2 ^ (prefixWord ++ tailWord_2389590).sum := by decide
  have hdescent : baseEnd_2389590 < baseStart_2389590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389614 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_2389614 : Nat := 118140960795 + 2389614 * 2 ^ 59
def prefixEnd_2389614 : Nat := 4983230072969 + 3 ^ 40 * 2389614 * 2
def baseEnd_2389614 : Nat := 272671235714026412874527

theorem tailTrace_2389614 : CollatzResearch.WordTrace tailWord_2389614 prefixEnd_2389614 272671235714026412874527 := by
  unfold tailWord_2389614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894547845605508303090987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58104255176562710949818597 10894547845605508303090987)
  ·
    refine ⟨16341821768408262454636481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10894547845605508303090987 16341821768408262454636481)
    ·
      refine ⟨12256366326306196840977361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16341821768408262454636481 12256366326306196840977361)
      ·
        refine ⟨9192274744729647630733021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12256366326306196840977361 9192274744729647630733021)
        ·
          refine ⟨3447103029273617861524883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9192274744729647630733021 3447103029273617861524883)
          ·
            refine ⟨5170654543910426792287325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447103029273617861524883 5170654543910426792287325)
            ·
              refine ⟨1938995453966410047107747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5170654543910426792287325 1938995453966410047107747)
              ·
                refine ⟨2908493180949615070661621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938995453966410047107747 2908493180949615070661621)
                ·
                  refine ⟨272671235714026412874527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2908493180949615070661621 272671235714026412874527)
                  ·
                    rfl

theorem cell22_2389614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_2389614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389614 prefixEnd_2389614 := by exact prefixLift 2389614
  have htrace : WordTrace (prefixWord ++ tailWord_2389614) baseStart_2389614 baseEnd_2389614 := by
    simpa [prefixWord, tailWord_2389614, baseEnd_2389614] using wordTrace_append hprefix tailTrace_2389614
  have hstable : (prefixWord ++ tailWord_2389614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389614).length < 2 ^ (prefixWord ++ tailWord_2389614).sum := by decide
  have hdescent : baseEnd_2389614 < baseStart_2389614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389655 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 4, 4]
def baseStart_2389655 : Nat := 118140960795 + 2389655 * 2 ^ 59
def prefixEnd_2389655 : Nat := 4983230072969 + 3 ^ 40 * 2389655 * 2
def baseEnd_2389655 : Nat := 818027742279968798348455

theorem tailTrace_2389655 : CollatzResearch.WordTrace tailWord_2389655 prefixEnd_2389655 818027742279968798348455 := by
  unfold tailWord_2389655
  simp only [CollatzResearch.WordTrace]
  refine ⟨87157878157695530426970419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58105252105130353617980279 87157878157695530426970419)
  ·
    refine ⟨130736817236543295640455629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87157878157695530426970419 130736817236543295640455629)
    ·
      refine ⟨49026306463703735865170861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130736817236543295640455629 49026306463703735865170861)
      ·
        refine ⟨18384864923888900949439073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49026306463703735865170861 18384864923888900949439073)
        ·
          refine ⟨13788648692916675712079305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18384864923888900949439073 13788648692916675712079305)
          ·
            refine ⟨10341486519687506784059479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13788648692916675712079305 10341486519687506784059479)
            ·
              refine ⟨15512229779531260176089219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10341486519687506784059479 15512229779531260176089219)
              ·
                refine ⟨23268344669296890264133829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15512229779531260176089219 23268344669296890264133829)
                ·
                  refine ⟨4362814625493166924525093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23268344669296890264133829 4362814625493166924525093)
                  ·
                    refine ⟨818027742279968798348455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362814625493166924525093 818027742279968798348455)
                    ·
                      rfl

theorem cell22_2389655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_2389655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389655 prefixEnd_2389655 := by exact prefixLift 2389655
  have htrace : WordTrace (prefixWord ++ tailWord_2389655) baseStart_2389655 baseEnd_2389655 := by
    simpa [prefixWord, tailWord_2389655, baseEnd_2389655] using wordTrace_append hprefix tailTrace_2389655
  have hstable : (prefixWord ++ tailWord_2389655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389655).length < 2 ^ (prefixWord ++ tailWord_2389655).sum := by decide
  have hdescent : baseEnd_2389655 < baseStart_2389655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389678 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2389678 : Nat := 118140960795 + 2389678 * 2 ^ 59
def prefixEnd_2389678 : Nat := 4983230072969 + 3 ^ 40 * 2389678 * 2
def baseEnd_2389678 : Nat := 818035615650004405023385

theorem tailTrace_2389678 : CollatzResearch.WordTrace tailWord_2389678 prefixEnd_2389678 818035615650004405023385 := by
  unfold tailWord_2389678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894839629576525669382211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58105811357741470236705125 10894839629576525669382211)
  ·
    refine ⟨16342259444364788504073317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10894839629576525669382211 16342259444364788504073317)
    ·
      refine ⟨3064173645818397844513747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16342259444364788504073317 3064173645818397844513747)
      ·
        refine ⟨4596260468727596766770621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3064173645818397844513747 4596260468727596766770621)
        ·
          refine ⟨1723597675772848787538983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4596260468727596766770621 1723597675772848787538983)
          ·
            refine ⟨2585396513659273181308475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723597675772848787538983 2585396513659273181308475)
            ·
              refine ⟨3878094770488909771962713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585396513659273181308475 3878094770488909771962713)
              ·
                refine ⟨2908571077866682328972035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3878094770488909771962713 2908571077866682328972035)
                ·
                  refine ⟨4362856616800023493458053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908571077866682328972035 4362856616800023493458053)
                  ·
                    refine ⟨818035615650004405023385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362856616800023493458053 818035615650004405023385)
                    ·
                      rfl

theorem cell22_2389678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2389678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389678 prefixEnd_2389678 := by exact prefixLift 2389678
  have htrace : WordTrace (prefixWord ++ tailWord_2389678) baseStart_2389678 baseEnd_2389678 := by
    simpa [prefixWord, tailWord_2389678, baseEnd_2389678] using wordTrace_append hprefix tailTrace_2389678
  have hstable : (prefixWord ++ tailWord_2389678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389678).length < 2 ^ (prefixWord ++ tailWord_2389678).sum := by decide
  have hdescent : baseEnd_2389678 < baseStart_2389678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389719 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 1, 3]
def baseStart_2389719 : Nat := 118140960795 + 2389719 * 2 ^ 59
def prefixEnd_2389719 : Nat := 4983230072969 + 3 ^ 40 * 2389719 * 2
def baseEnd_2389719 : Nat := 818049650787893964748259

theorem tailTrace_2389719 : CollatzResearch.WordTrace tailWord_2389719 prefixEnd_2389719 818049650787893964748259 := by
  unfold tailWord_2389719
  simp only [CollatzResearch.WordTrace]
  refine ⟨87160212429463669357300211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58106808286309112904866807 87160212429463669357300211)
  ·
    refine ⟨130740318644195504035950317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87160212429463669357300211 130740318644195504035950317)
    ·
      refine ⟨49027619491573314013481369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130740318644195504035950317 49027619491573314013481369)
      ·
        refine ⟨36770714618679985510111027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49027619491573314013481369 36770714618679985510111027)
        ·
          refine ⟨55156071928019978265166541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36770714618679985510111027 55156071928019978265166541)
          ·
            refine ⟨20683526973007491849437453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55156071928019978265166541 20683526973007491849437453)
            ·
              refine ⟨7756322614877809443539045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20683526973007491849437453 7756322614877809443539045)
              ·
                refine ⟨1454310490289589270663571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7756322614877809443539045 1454310490289589270663571)
                ·
                  refine ⟨2181465735434383905995357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454310490289589270663571 2181465735434383905995357)
                  ·
                    refine ⟨818049650787893964748259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181465735434383905995357 818049650787893964748259)
                    ·
                      rfl

theorem cell22_2389719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_2389719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389719 prefixEnd_2389719 := by exact prefixLift 2389719
  have htrace : WordTrace (prefixWord ++ tailWord_2389719) baseStart_2389719 baseEnd_2389719 := by
    simpa [prefixWord, tailWord_2389719, baseEnd_2389719] using wordTrace_append hprefix tailTrace_2389719
  have hstable : (prefixWord ++ tailWord_2389719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389719).length < 2 ^ (prefixWord ++ tailWord_2389719).sum := by decide
  have hdescent : baseEnd_2389719 < baseStart_2389719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389811 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 4]
def baseStart_2389811 : Nat := 118140960795 + 2389811 * 2 ^ 59
def prefixEnd_2389811 : Nat := 4983230072969 + 3 ^ 40 * 2389811 * 2
def baseEnd_2389811 : Nat := 272693714756012130482659

theorem tailTrace_2389811 : CollatzResearch.WordTrace tailWord_2389811 prefixEnd_2389811 272693714756012130482659 := by
  unfold tailWord_2389811
  simp only [CollatzResearch.WordTrace]
  refine ⟨87163567945130369069649287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58109045296753579379766191 87163567945130369069649287)
  ·
    refine ⟨130745351917695553604473931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87163567945130369069649287 130745351917695553604473931)
    ·
      refine ⟨196118027876543330406710897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130745351917695553604473931 196118027876543330406710897)
      ·
        refine ⟨147088520907407497805033173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196118027876543330406710897 147088520907407497805033173)
        ·
          refine ⟨3447387208767363229805465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 147088520907407497805033173 3447387208767363229805465)
          ·
            refine ⟨2585540406575522422354099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3447387208767363229805465 2585540406575522422354099)
            ·
              refine ⟨3878310609863283633531149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585540406575522422354099 3878310609863283633531149)
              ·
                refine ⟨1454366478698731362574181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3878310609863283633531149 1454366478698731362574181)
                ·
                  refine ⟨272693714756012130482659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454366478698731362574181 272693714756012130482659)
                  ·
                    rfl

theorem cell22_2389811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 4].length) (baseStart_2389811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389811 prefixEnd_2389811 := by exact prefixLift 2389811
  have htrace : WordTrace (prefixWord ++ tailWord_2389811) baseStart_2389811 baseEnd_2389811 := by
    simpa [prefixWord, tailWord_2389811, baseEnd_2389811] using wordTrace_append hprefix tailTrace_2389811
  have hstable : (prefixWord ++ tailWord_2389811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389811).length < 2 ^ (prefixWord ++ tailWord_2389811).sum := by decide
  have hdescent : baseEnd_2389811 < baseStart_2389811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389822 : List Nat := [4, 2, 1, 2, 2, 1, 10]
def baseStart_2389822 : Nat := 118140960795 + 2389822 * 2 ^ 59
def prefixEnd_2389822 : Nat := 4983230072969 + 3 ^ 40 * 2389822 * 2
def baseEnd_2389822 : Nat := 30299441103438371460109

theorem tailTrace_2389822 : CollatzResearch.WordTrace tailWord_2389822 prefixEnd_2389822 30299441103438371460109 := by
  unfold tailWord_2389822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895496143511314743537465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58109312765393678632199813 10895496143511314743537465)
  ·
    refine ⟨8171622107633486057653099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10895496143511314743537465 8171622107633486057653099)
    ·
      refine ⟨12257433161450229086479649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8171622107633486057653099 12257433161450229086479649)
      ·
        refine ⟨9193074871087671814859737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12257433161450229086479649 9193074871087671814859737)
        ·
          refine ⟨6894806153315753861144803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9193074871087671814859737 6894806153315753861144803)
          ·
            refine ⟨10342209229973630791717205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6894806153315753861144803 10342209229973630791717205)
            ·
              refine ⟨30299441103438371460109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10342209229973630791717205 30299441103438371460109)
              ·
                rfl

theorem cell22_2389822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 10].length) (baseStart_2389822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389822 prefixEnd_2389822 := by exact prefixLift 2389822
  have htrace : WordTrace (prefixWord ++ tailWord_2389822) baseStart_2389822 baseEnd_2389822 := by
    simpa [prefixWord, tailWord_2389822, baseEnd_2389822] using wordTrace_append hprefix tailTrace_2389822
  have hstable : (prefixWord ++ tailWord_2389822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389822).length < 2 ^ (prefixWord ++ tailWord_2389822).sum := by decide
  have hdescent : baseEnd_2389822 < baseStart_2389822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389897 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_2389897 : Nat := 118140960795 + 2389897 * 2 ^ 59
def prefixEnd_2389897 : Nat := 4983230072969 + 3 ^ 40 * 2389897 * 2
def baseEnd_2389897 : Nat := 818110583825560833797713

theorem tailTrace_2389897 : CollatzResearch.WordTrace tailWord_2389897 prefixEnd_2389897 818110583825560833797713 := by
  unfold tailWord_2389897
  simp only [CollatzResearch.WordTrace]
  refine ⟨87166704622818805757279945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58111136415212537171519963 87166704622818805757279945)
  ·
    refine ⟨65375028467114104317959959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87166704622818805757279945 65375028467114104317959959)
    ·
      refine ⟨98062542700671156476939939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65375028467114104317959959 98062542700671156476939939)
      ·
        refine ⟨147093814051006734715409909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98062542700671156476939939 147093814051006734715409909)
        ·
          refine ⟨13790045067281881379569679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147093814051006734715409909 13790045067281881379569679)
          ·
            refine ⟨20685067600922822069354519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13790045067281881379569679 20685067600922822069354519)
            ·
              refine ⟨31027601401384233104031779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20685067600922822069354519 31027601401384233104031779)
              ·
                refine ⟨46541402102076349656047669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31027601401384233104031779 46541402102076349656047669)
                ·
                  refine ⟨4363256447069657780254469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46541402102076349656047669 4363256447069657780254469)
                  ·
                    refine ⟨818110583825560833797713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363256447069657780254469 818110583825560833797713)
                    ·
                      rfl

theorem cell22_2389897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_2389897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389897 prefixEnd_2389897 := by exact prefixLift 2389897
  have htrace : WordTrace (prefixWord ++ tailWord_2389897) baseStart_2389897 baseEnd_2389897 := by
    simpa [prefixWord, tailWord_2389897, baseEnd_2389897] using wordTrace_append hprefix tailTrace_2389897
  have hstable : (prefixWord ++ tailWord_2389897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389897).length < 2 ^ (prefixWord ++ tailWord_2389897).sum := by decide
  have hdescent : baseEnd_2389897 < baseStart_2389897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389914 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_2389914 : Nat := 118140960795 + 2389914 * 2 ^ 59
def prefixEnd_2389914 : Nat := 4983230072969 + 3 ^ 40 * 2389914 * 2
def baseEnd_2389914 : Nat := 818116403272978456122661

theorem tailTrace_2389914 : CollatzResearch.WordTrace tailWord_2389914 prefixEnd_2389914 818116403272978456122661 := by
  unfold tailWord_2389914
  simp only [CollatzResearch.WordTrace]
  refine ⟨21791831165939304415162199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58111549775838145107099197 21791831165939304415162199)
  ·
    refine ⟨32687746748908956622743299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21791831165939304415162199 32687746748908956622743299)
    ·
      refine ⟨49031620123363434934114949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32687746748908956622743299 49031620123363434934114949)
      ·
        refine ⟨9193428773130644050146553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49031620123363434934114949 9193428773130644050146553)
        ·
          refine ⟨6895071579847983037609915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9193428773130644050146553 6895071579847983037609915)
          ·
            refine ⟨10342607369771974556414873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895071579847983037609915 10342607369771974556414873)
            ·
              refine ⟨7756955527328980917311155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10342607369771974556414873 7756955527328980917311155)
              ·
                refine ⟨11635433290993471375966733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7756955527328980917311155 11635433290993471375966733)
                ·
                  refine ⟨4363287484122551765987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11635433290993471375966733 4363287484122551765987525)
                  ·
                    refine ⟨818116403272978456122661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363287484122551765987525 818116403272978456122661)
                    ·
                      rfl

theorem cell22_2389914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_2389914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389914 prefixEnd_2389914 := by exact prefixLift 2389914
  have htrace : WordTrace (prefixWord ++ tailWord_2389914) baseStart_2389914 baseEnd_2389914 := by
    simpa [prefixWord, tailWord_2389914, baseEnd_2389914] using wordTrace_append hprefix tailTrace_2389914
  have hstable : (prefixWord ++ tailWord_2389914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389914).length < 2 ^ (prefixWord ++ tailWord_2389914).sum := by decide
  have hdescent : baseEnd_2389914 < baseStart_2389914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389944 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_2389944 : Nat := 118140960795 + 2389944 * 2 ^ 59
def prefixEnd_2389944 : Nat := 4983230072969 + 3 ^ 40 * 2389944 * 2
def baseEnd_2389944 : Nat := 818126672886068377872569

theorem tailTrace_2389944 : CollatzResearch.WordTrace tailWord_2389944 prefixEnd_2389944 818126672886068377872569 := by
  unfold tailWord_2389944
  simp only [CollatzResearch.WordTrace]
  refine ⟨43584209426824266392120443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58112279235765688522827257 43584209426824266392120443)
  ·
    refine ⟨65376314140236399588180665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43584209426824266392120443 65376314140236399588180665)
    ·
      refine ⟨49032235605177299691135499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65376314140236399588180665 49032235605177299691135499)
      ·
        refine ⟨73548353407765949536703249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49032235605177299691135499 73548353407765949536703249)
        ·
          refine ⟨55161265055824462152527437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73548353407765949536703249 55161265055824462152527437)
          ·
            refine ⟨20685474395934173307197789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55161265055824462152527437 20685474395934173307197789)
            ·
              refine ⟨7757052898475314990199171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20685474395934173307197789 7757052898475314990199171)
              ·
                refine ⟨11635579347712972485298757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757052898475314990199171 11635579347712972485298757)
                ·
                  refine ⟨2181671127696182340993517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11635579347712972485298757 2181671127696182340993517)
                  ·
                    refine ⟨818126672886068377872569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181671127696182340993517 818126672886068377872569)
                    ·
                      rfl

theorem cell22_2389944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_2389944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389944 prefixEnd_2389944 := by exact prefixLift 2389944
  have htrace : WordTrace (prefixWord ++ tailWord_2389944) baseStart_2389944 baseEnd_2389944 := by
    simpa [prefixWord, tailWord_2389944, baseEnd_2389944] using wordTrace_append hprefix tailTrace_2389944
  have hstable : (prefixWord ++ tailWord_2389944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389944).length < 2 ^ (prefixWord ++ tailWord_2389944).sum := by decide
  have hdescent : baseEnd_2389944 < baseStart_2389944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389991 : List Nat := [1, 1, 5, 2, 4, 1, 8]
def baseStart_2389991 : Nat := 118140960795 + 2389991 * 2 ^ 59
def prefixEnd_2389991 : Nat := 4983230072969 + 3 ^ 40 * 2389991 * 2
def baseEnd_2389991 : Nat := 30301583775799108220275

theorem tailTrace_2389991 : CollatzResearch.WordTrace tailWord_2389991 prefixEnd_2389991 30301583775799108220275 := by
  unfold tailWord_2389991
  simp only [CollatzResearch.WordTrace]
  refine ⟨87170133084478259811201827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58113422056318839874134551 87170133084478259811201827)
  ·
    refine ⟨130755199626717389716802741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87170133084478259811201827 130755199626717389716802741)
    ·
      refine ⟨12258299965004755285950257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130755199626717389716802741 12258299965004755285950257)
      ·
        refine ⟨9193724973753566464462693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12258299965004755285950257 9193724973753566464462693)
        ·
          refine ⟨1723823432578793712086755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9193724973753566464462693 1723823432578793712086755)
          ·
            refine ⟨2585735148868190568130133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723823432578793712086755 2585735148868190568130133)
            ·
              refine ⟨30301583775799108220275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2585735148868190568130133 30301583775799108220275)
              ·
                rfl

theorem cell22_2389991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 8].length) (baseStart_2389991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389991 prefixEnd_2389991 := by exact prefixLift 2389991
  have htrace : WordTrace (prefixWord ++ tailWord_2389991) baseStart_2389991 baseEnd_2389991 := by
    simpa [prefixWord, tailWord_2389991, baseEnd_2389991] using wordTrace_append hprefix tailTrace_2389991
  have hstable : (prefixWord ++ tailWord_2389991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389991).length < 2 ^ (prefixWord ++ tailWord_2389991).sum := by decide
  have hdescent : baseEnd_2389991 < baseStart_2389991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390032 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_2390032 : Nat := 118140960795 + 2390032 * 2 ^ 59
def prefixEnd_2390032 : Nat := 4983230072969 + 3 ^ 40 * 2390032 * 2
def baseEnd_2390032 : Nat := 818156797084465481672299

theorem tailTrace_2390032 : CollatzResearch.WordTrace tailWord_2390032 prefixEnd_2390032 818156797084465481672299 := by
  unfold tailWord_2390032
  simp only [CollatzResearch.WordTrace]
  refine ⟨43585814238664861906722175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58114418984886482542296233 43585814238664861906722175)
  ·
    refine ⟨65378721357997292860083263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43585814238664861906722175 65378721357997292860083263)
    ·
      refine ⟨98068082036995939290124895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65378721357997292860083263 98068082036995939290124895)
      ·
        refine ⟨147102123055493908935187343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98068082036995939290124895 147102123055493908935187343)
        ·
          refine ⟨220653184583240863402781015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147102123055493908935187343 220653184583240863402781015)
          ·
            refine ⟨330979776874861295104171523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220653184583240863402781015 330979776874861295104171523)
            ·
              refine ⟨496469665312291942656257285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330979776874861295104171523 496469665312291942656257285)
              ·
                refine ⟨93088062246054739248048241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 496469665312291942656257285 93088062246054739248048241)
                ·
                  refine ⟨69816046684541054436036181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93088062246054739248048241 69816046684541054436036181)
                  ·
                    refine ⟨818156797084465481672299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69816046684541054436036181 818156797084465481672299)
                    ·
                      rfl

theorem cell22_2390032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_2390032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390032 prefixEnd_2390032 := by exact prefixLift 2390032
  have htrace : WordTrace (prefixWord ++ tailWord_2390032) baseStart_2390032 baseEnd_2390032 := by
    simpa [prefixWord, tailWord_2390032, baseEnd_2390032] using wordTrace_append hprefix tailTrace_2390032
  have hstable : (prefixWord ++ tailWord_2390032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390032).length < 2 ^ (prefixWord ++ tailWord_2390032).sum := by decide
  have hdescent : baseEnd_2390032 < baseStart_2390032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390068 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2390068 : Nat := 118140960795 + 2390068 * 2 ^ 59
def prefixEnd_2390068 : Nat := 4983230072969 + 3 ^ 40 * 2390068 * 2
def baseEnd_2390068 : Nat := 818169120620173387772189

theorem tailTrace_2390068 : CollatzResearch.WordTrace tailWord_2390068 prefixEnd_2390068 818169120620173387772189 := by
  unfold tailWord_2390068
  simp only [CollatzResearch.WordTrace]
  refine ⟨43586470752599650980877429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58115294336799534641169905 43586470752599650980877429)
  ·
    refine ⟨4086231633056217279457259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43586470752599650980877429 4086231633056217279457259)
    ·
      refine ⟨6129347449584325919185889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086231633056217279457259 6129347449584325919185889)
      ·
        refine ⟨4597010587188244439389417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6129347449584325919185889 4597010587188244439389417)
        ·
          refine ⟨3447757940391183329542063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4597010587188244439389417 3447757940391183329542063)
          ·
            refine ⟨5171636910586774994313095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447757940391183329542063 5171636910586774994313095)
            ·
              refine ⟨7757455365880162491469643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171636910586774994313095 7757455365880162491469643)
              ·
                refine ⟨11636183048820243737204465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757455365880162491469643 11636183048820243737204465)
                ·
                  refine ⟨8727137286615182802903349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11636183048820243737204465 8727137286615182802903349)
                  ·
                    refine ⟨818169120620173387772189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8727137286615182802903349 818169120620173387772189)
                    ·
                      rfl

theorem cell22_2390068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2390068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390068 prefixEnd_2390068 := by exact prefixLift 2390068
  have htrace : WordTrace (prefixWord ++ tailWord_2390068) baseStart_2390068 baseEnd_2390068 := by
    simpa [prefixWord, tailWord_2390068, baseEnd_2390068] using wordTrace_append hprefix tailTrace_2390068
  have hstable : (prefixWord ++ tailWord_2390068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390068).length < 2 ^ (prefixWord ++ tailWord_2390068).sum := by decide
  have hdescent : baseEnd_2390068 < baseStart_2390068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390079 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 1, 5]
def baseStart_2390079 : Nat := 118140960795 + 2390079 * 2 ^ 59
def prefixEnd_2390079 : Nat := 4983230072969 + 3 ^ 40 * 2390079 * 2
def baseEnd_2390079 : Nat := 818172886144973025747155

theorem tailTrace_2390079 : CollatzResearch.WordTrace tailWord_2390079 prefixEnd_2390079 818172886144973025747155 := by
  unfold tailWord_2390079
  simp only [CollatzResearch.WordTrace]
  refine ⟨87173342708159450840405291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58115561805439633893603527 87173342708159450840405291)
  ·
    refine ⟨130760014062239176260607937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87173342708159450840405291 130760014062239176260607937)
    ·
      refine ⟨98070010546679382195455953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130760014062239176260607937 98070010546679382195455953)
      ·
        refine ⟨73552507910009536646591965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98070010546679382195455953 73552507910009536646591965)
        ·
          refine ⟨27582190466253576242471987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73552507910009536646591965 27582190466253576242471987)
          ·
            refine ⟨41373285699380364363707981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27582190466253576242471987 41373285699380364363707981)
            ·
              refine ⟨15514982137267636636390493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41373285699380364363707981 15514982137267636636390493)
              ·
                refine ⟨5818118301475363738646435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15514982137267636636390493 5818118301475363738646435)
                ·
                  refine ⟨8727177452213045607969653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5818118301475363738646435 8727177452213045607969653)
                  ·
                    refine ⟨818172886144973025747155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8727177452213045607969653 818172886144973025747155)
                    ·
                      rfl

theorem cell22_2390079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_2390079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390079 prefixEnd_2390079 := by exact prefixLift 2390079
  have htrace : WordTrace (prefixWord ++ tailWord_2390079) baseStart_2390079 baseEnd_2390079 := by
    simpa [prefixWord, tailWord_2390079, baseEnd_2390079] using wordTrace_append hprefix tailTrace_2390079
  have hstable : (prefixWord ++ tailWord_2390079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390079).length < 2 ^ (prefixWord ++ tailWord_2390079).sum := by decide
  have hdescent : baseEnd_2390079 < baseStart_2390079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390081 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 6]
def baseStart_2390081 : Nat := 118140960795 + 2390081 * 2 ^ 59
def prefixEnd_2390081 : Nat := 4983230072969 + 3 ^ 40 * 2390081 * 2
def baseEnd_2390081 : Nat := 272724523595281895732383

theorem tailTrace_2390081 : CollatzResearch.WordTrace tailWord_2390081 prefixEnd_2390081 272724523595281895732383 := by
  unfold tailWord_2390081
  simp only [CollatzResearch.WordTrace]
  refine ⟨87173415654152205181978097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58115610436101470121318731 87173415654152205181978097)
  ·
    refine ⟨65380061740614153886483573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87173415654152205181978097 65380061740614153886483573)
    ·
      refine ⟨6129380788182576926857835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65380061740614153886483573 6129380788182576926857835)
      ·
        refine ⟨9194071182273865390286753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6129380788182576926857835 9194071182273865390286753)
        ·
          refine ⟨6895553386705399042715065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9194071182273865390286753 6895553386705399042715065)
          ·
            refine ⟨5171665040029049282036299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6895553386705399042715065 5171665040029049282036299)
            ·
              refine ⟨7757497560043573923054449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171665040029049282036299 7757497560043573923054449)
              ·
                refine ⟨5818123170032680442290837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7757497560043573923054449 5818123170032680442290837)
                ·
                  refine ⟨272724523595281895732383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5818123170032680442290837 272724523595281895732383)
                  ·
                    rfl

theorem cell22_2390081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_2390081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390081 prefixEnd_2390081 := by exact prefixLift 2390081
  have htrace : WordTrace (prefixWord ++ tailWord_2390081) baseStart_2390081 baseEnd_2390081 := by
    simpa [prefixWord, tailWord_2390081, baseEnd_2390081] using wordTrace_append hprefix tailTrace_2390081
  have hstable : (prefixWord ++ tailWord_2390081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390081).length < 2 ^ (prefixWord ++ tailWord_2390081).sum := by decide
  have hdescent : baseEnd_2390081 < baseStart_2390081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390130 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_2390130 : Nat := 118140960795 + 2390130 * 2 ^ 59
def prefixEnd_2390130 : Nat := 4983230072969 + 3 ^ 40 * 2390130 * 2
def baseEnd_2390130 : Nat := 818190344487225892721999

theorem tailTrace_2390130 : CollatzResearch.WordTrace tailWord_2390130 prefixEnd_2390130 818190344487225892721999 := by
  unfold tailWord_2390130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793800707743671637627961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58116801887316457700341229 21793800707743671637627961)
  ·
    refine ⟨16345350530807753728220971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21793800707743671637627961 16345350530807753728220971)
    ·
      refine ⟨24518025796211630592331457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16345350530807753728220971 24518025796211630592331457)
      ·
        refine ⟨18388519347158722944248593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24518025796211630592331457 18388519347158722944248593)
        ·
          refine ⟨13791389510369042208186445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18388519347158722944248593 13791389510369042208186445)
          ·
            refine ⟨5171771066388390828069917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13791389510369042208186445 5171771066388390828069917)
            ·
              refine ⟨1939414149895646560526219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5171771066388390828069917 1939414149895646560526219)
              ·
                refine ⟨2909121224843469840789329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939414149895646560526219 2909121224843469840789329)
                ·
                  refine ⟨2181840918632602380591997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2909121224843469840789329 2181840918632602380591997)
                  ·
                    refine ⟨818190344487225892721999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181840918632602380591997 818190344487225892721999)
                    ·
                      rfl

theorem cell22_2390130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_2390130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390130 prefixEnd_2390130 := by exact prefixLift 2390130
  have htrace : WordTrace (prefixWord ++ tailWord_2390130) baseStart_2390130 baseEnd_2390130 := by
    simpa [prefixWord, tailWord_2390130, baseEnd_2390130] using wordTrace_append hprefix tailTrace_2390130
  have hstable : (prefixWord ++ tailWord_2390130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390130).length < 2 ^ (prefixWord ++ tailWord_2390130).sum := by decide
  have hdescent : baseEnd_2390130 < baseStart_2390130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390166 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2390166 : Nat := 118140960795 + 2390166 * 2 ^ 59
def prefixEnd_2390166 : Nat := 4983230072969 + 3 ^ 40 * 2390166 * 2
def baseEnd_2390166 : Nat := 272734222674311266273963

theorem tailTrace_2390166 : CollatzResearch.WordTrace tailWord_2390166 prefixEnd_2390166 272734222674311266273963 := by
  unfold tailWord_2390166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448532241177766543676397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58117677239229509799214901 5448532241177766543676397)
  ·
    refine ⟨2043199590441662453878649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5448532241177766543676397 2043199590441662453878649)
    ·
      refine ⟨1532399692831246840408987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2043199590441662453878649 1532399692831246840408987)
      ·
        refine ⟨2298599539246870260613481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532399692831246840408987 2298599539246870260613481)
        ·
          refine ⟨1723949654435152695460111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298599539246870260613481 1723949654435152695460111)
          ·
            refine ⟨2585924481652729043190167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723949654435152695460111 2585924481652729043190167)
            ·
              refine ⟨3878886722479093564785251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585924481652729043190167 3878886722479093564785251)
              ·
                refine ⟨5818330083718640347177877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878886722479093564785251 5818330083718640347177877)
                ·
                  refine ⟨272734222674311266273963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5818330083718640347177877 272734222674311266273963)
                  ·
                    rfl

theorem cell22_2390166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2390166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390166 prefixEnd_2390166 := by exact prefixLift 2390166
  have htrace : WordTrace (prefixWord ++ tailWord_2390166) baseStart_2390166 baseEnd_2390166 := by
    simpa [prefixWord, tailWord_2390166, baseEnd_2390166] using wordTrace_append hprefix tailTrace_2390166
  have hstable : (prefixWord ++ tailWord_2390166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390166).length < 2 ^ (prefixWord ++ tailWord_2390166).sum := by decide
  have hdescent : baseEnd_2390166 < baseStart_2390166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390169 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_2390169 : Nat := 118140960795 + 2390169 * 2 ^ 59
def prefixEnd_2390169 : Nat := 4983230072969 + 3 ^ 40 * 2390169 * 2
def baseEnd_2390169 : Nat := 818203694984242790996879

theorem tailTrace_2390169 : CollatzResearch.WordTrace tailWord_2390169 prefixEnd_2390169 818203694984242790996879 := by
  unfold tailWord_2390169
  simp only [CollatzResearch.WordTrace]
  refine ⟨87176625277833396211181561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58117750185222264140787707 87176625277833396211181561)
  ·
    refine ⟨65382468958375047158386171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87176625277833396211181561 65382468958375047158386171)
    ·
      refine ⟨98073703437562570737579257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65382468958375047158386171 98073703437562570737579257)
      ·
        refine ⟨73555277578171928053184443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98073703437562570737579257 73555277578171928053184443)
        ·
          refine ⟨110332916367257892079776665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73555277578171928053184443 110332916367257892079776665)
          ·
            refine ⟨82749687275443419059832499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110332916367257892079776665 82749687275443419059832499)
            ·
              refine ⟨124124530913165128589748749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82749687275443419059832499 124124530913165128589748749)
              ·
                refine ⟨46546699092436923221155781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124124530913165128589748749 46546699092436923221155781)
                ·
                  refine ⟨8727506079831923103966709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46546699092436923221155781 8727506079831923103966709)
                  ·
                    refine ⟨818203694984242790996879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8727506079831923103966709 818203694984242790996879)
                    ·
                      rfl

theorem cell22_2390169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_2390169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390169 prefixEnd_2390169 := by exact prefixLift 2390169
  have htrace : WordTrace (prefixWord ++ tailWord_2390169) baseStart_2390169 baseEnd_2390169 := by
    simpa [prefixWord, tailWord_2390169, baseEnd_2390169] using wordTrace_append hprefix tailTrace_2390169
  have hstable : (prefixWord ++ tailWord_2390169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390169).length < 2 ^ (prefixWord ++ tailWord_2390169).sum := by decide
  have hdescent : baseEnd_2390169 < baseStart_2390169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390175 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 3, 3]
def baseStart_2390175 : Nat := 118140960795 + 2390175 * 2 ^ 59
def prefixEnd_2390175 : Nat := 4983230072969 + 3 ^ 40 * 2390175 * 2
def baseEnd_2390175 : Nat := 818205748906860775346861

theorem tailTrace_2390175 : CollatzResearch.WordTrace tailWord_2390175 prefixEnd_2390175 818205748906860775346861 := by
  unfold tailWord_2390175
  simp only [CollatzResearch.WordTrace]
  refine ⟨87176844115811659235899979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58117896077207772823933319 87176844115811659235899979)
  ·
    refine ⟨130765266173717488853849969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87176844115811659235899979 130765266173717488853849969)
    ·
      refine ⟨98073949630288116640387477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130765266173717488853849969 98073949630288116640387477)
      ·
        refine ⟨4597216388919755467518163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98073949630288116640387477 4597216388919755467518163)
        ·
          refine ⟨6895824583379633201277245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597216388919755467518163 6895824583379633201277245)
          ·
            refine ⟨2585934218767362450478967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6895824583379633201277245 2585934218767362450478967)
            ·
              refine ⟨3878901328151043675718451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585934218767362450478967 3878901328151043675718451)
              ·
                refine ⟨5818351992226565513577677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878901328151043675718451 5818351992226565513577677)
                ·
                  refine ⟨2181881997084962067591629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5818351992226565513577677 2181881997084962067591629)
                  ·
                    refine ⟨818205748906860775346861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181881997084962067591629 818205748906860775346861)
                    ·
                      rfl

theorem cell22_2390175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_2390175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390175 prefixEnd_2390175 := by exact prefixLift 2390175
  have htrace : WordTrace (prefixWord ++ tailWord_2390175) baseStart_2390175 baseEnd_2390175 := by
    simpa [prefixWord, tailWord_2390175, baseEnd_2390175] using wordTrace_append hprefix tailTrace_2390175
  have hstable : (prefixWord ++ tailWord_2390175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390175).length < 2 ^ (prefixWord ++ tailWord_2390175).sum := by decide
  have hdescent : baseEnd_2390175 < baseStart_2390175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390201 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_2390201 : Nat := 118140960795 + 2390201 * 2 ^ 59
def prefixEnd_2390201 : Nat := 4983230072969 + 3 ^ 40 * 2390201 * 2
def baseEnd_2390201 : Nat := 818214649238205374196781

theorem tailTrace_2390201 : CollatzResearch.WordTrace tailWord_2390201 prefixEnd_2390201 818214649238205374196781 := by
  unfold tailWord_2390201
  simp only [CollatzResearch.WordTrace]
  refine ⟨87177792413717465676346457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58118528275811643784230971 87177792413717465676346457)
  ·
    refine ⟨65383344310288099257259843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87177792413717465676346457 65383344310288099257259843)
    ·
      refine ⟨98075016465432148885889765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65383344310288099257259843 98075016465432148885889765)
      ·
        refine ⟨18389065587268527916104331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98075016465432148885889765 18389065587268527916104331)
        ·
          refine ⟨27583598380902791874156497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18389065587268527916104331 27583598380902791874156497)
          ·
            refine ⟨20687698785677093905617373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27583598380902791874156497 20687698785677093905617373)
            ·
              refine ⟨7757887044628910214606515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20687698785677093905617373 7757887044628910214606515)
              ·
                refine ⟨11636830566943365321909773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757887044628910214606515 11636830566943365321909773)
                ·
                  refine ⟨4363811462603761995716165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11636830566943365321909773 4363811462603761995716165)
                  ·
                    refine ⟨818214649238205374196781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363811462603761995716165 818214649238205374196781)
                    ·
                      rfl

theorem cell22_2390201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_2390201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390201 prefixEnd_2390201 := by exact prefixLift 2390201
  have htrace : WordTrace (prefixWord ++ tailWord_2390201) baseStart_2390201 baseEnd_2390201 := by
    simpa [prefixWord, tailWord_2390201, baseEnd_2390201] using wordTrace_append hprefix tailTrace_2390201
  have hstable : (prefixWord ++ tailWord_2390201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390201).length < 2 ^ (prefixWord ++ tailWord_2390201).sum := by decide
  have hdescent : baseEnd_2390201 < baseStart_2390201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390248 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2390248 : Nat := 118140960795 + 2390248 * 2 ^ 59
def prefixEnd_2390248 : Nat := 4983230072969 + 3 ^ 40 * 2390248 * 2
def baseEnd_2390248 : Nat := 818230738298712918271637

theorem tailTrace_2390248 : CollatzResearch.WordTrace tailWord_2390248 prefixEnd_2390248 818230738298712918271637 := by
  unfold tailWord_2390248
  simp only [CollatzResearch.WordTrace]
  refine ⟨43589753322273596351653699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58119671096364795135538265 43589753322273596351653699)
  ·
    refine ⟨65384629983410394527480549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43589753322273596351653699 65384629983410394527480549)
    ·
      refine ⟨12259618121889448973902603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65384629983410394527480549 12259618121889448973902603)
      ·
        refine ⟨18389427182834173460853905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12259618121889448973902603 18389427182834173460853905)
        ·
          refine ⟨13792070387125630095640429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18389427182834173460853905 13792070387125630095640429)
          ·
            refine ⟨5172026395172111285865161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13792070387125630095640429 5172026395172111285865161)
            ·
              refine ⟨3879019796379083464398871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5172026395172111285865161 3879019796379083464398871)
              ·
                refine ⟨5818529694568625196598307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879019796379083464398871 5818529694568625196598307)
                ·
                  refine ⟨8727794541852937794897461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5818529694568625196598307 8727794541852937794897461)
                  ·
                    refine ⟨818230738298712918271637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8727794541852937794897461 818230738298712918271637)
                    ·
                      rfl

theorem cell22_2390248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2390248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390248 prefixEnd_2390248 := by exact prefixLift 2390248
  have htrace : WordTrace (prefixWord ++ tailWord_2390248) baseStart_2390248 baseEnd_2390248 := by
    simpa [prefixWord, tailWord_2390248, baseEnd_2390248] using wordTrace_append hprefix tailTrace_2390248
  have hstable : (prefixWord ++ tailWord_2390248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390248).length < 2 ^ (prefixWord ++ tailWord_2390248).sum := by decide
  have hdescent : baseEnd_2390248 < baseStart_2390248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390293 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2390293 : Nat := 118140960795 + 2390293 * 2 ^ 59
def prefixEnd_2390293 : Nat := 4983230072969 + 3 ^ 40 * 2390293 * 2
def baseEnd_2390293 : Nat := 818246142718347800896499

theorem tailTrace_2390293 : CollatzResearch.WordTrace tailWord_2390293 prefixEnd_2390293 818246142718347800896499 := by
  unfold tailWord_2390293
  simp only [CollatzResearch.WordTrace]
  refine ⟨87181147929384165388695533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58120765286256110259130355 87181147929384165388695533)
  ·
    refine ⟨32692930473519062020760825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87181147929384165388695533 32692930473519062020760825)
    ·
      refine ⟨24519697855139296515570619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32692930473519062020760825 24519697855139296515570619)
      ·
        refine ⟨36779546782708944773355929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24519697855139296515570619 36779546782708944773355929)
        ·
          refine ⟨27584660087031708580016947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36779546782708944773355929 27584660087031708580016947)
          ·
            refine ⟨41376990130547562870025421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27584660087031708580016947 41376990130547562870025421)
            ·
              refine ⟨15516371298955336076259533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41376990130547562870025421 15516371298955336076259533)
              ·
                refine ⟨5818639237108251028597325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15516371298955336076259533 5818639237108251028597325)
                ·
                  refine ⟨2181989713915594135723997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5818639237108251028597325 2181989713915594135723997)
                  ·
                    refine ⟨818246142718347800896499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181989713915594135723997 818246142718347800896499)
                    ·
                      rfl

theorem cell22_2390293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2390293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390293 prefixEnd_2390293 := by exact prefixLift 2390293
  have htrace : WordTrace (prefixWord ++ tailWord_2390293) baseStart_2390293 baseEnd_2390293 := by
    simpa [prefixWord, tailWord_2390293, baseEnd_2390293] using wordTrace_append hprefix tailTrace_2390293
  have hstable : (prefixWord ++ tailWord_2390293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390293).length < 2 ^ (prefixWord ++ tailWord_2390293).sum := by decide
  have hdescent : baseEnd_2390293 < baseStart_2390293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390312 : List Nat := [2, 1, 5, 1, 4, 1, 2, 6]
def baseStart_2390312 : Nat := 118140960795 + 2390312 * 2 ^ 59
def prefixEnd_2390312 : Nat := 4983230072969 + 3 ^ 40 * 2390312 * 2
def baseEnd_2390312 : Nat := 90916960756293120519049

theorem tailTrace_2390312 : CollatzResearch.WordTrace tailWord_2390312 prefixEnd_2390312 90916960756293120519049 := by
  unfold tailWord_2390312
  simp only [CollatzResearch.WordTrace]
  refine ⟨43590920458157665816818595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58121227277543554422424793 43590920458157665816818595)
  ·
    refine ⟨65386380687236498725227893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43590920458157665816818595 65386380687236498725227893)
    ·
      refine ⟨6129973189428421755490115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65386380687236498725227893 6129973189428421755490115)
      ·
        refine ⟨9194959784142632633235173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6129973189428421755490115 9194959784142632633235173)
        ·
          refine ⟨1724054959526743618731595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9194959784142632633235173 1724054959526743618731595)
          ·
            refine ⟨2586082439290115428097393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724054959526743618731595 2586082439290115428097393)
            ·
              refine ⟨1939561829467586571073045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586082439290115428097393 1939561829467586571073045)
              ·
                refine ⟨90916960756293120519049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1939561829467586571073045 90916960756293120519049)
                ·
                  rfl

theorem cell22_2390312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_2390312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390312 prefixEnd_2390312 := by exact prefixLift 2390312
  have htrace : WordTrace (prefixWord ++ tailWord_2390312) baseStart_2390312 baseEnd_2390312 := by
    simpa [prefixWord, tailWord_2390312, baseEnd_2390312] using wordTrace_append hprefix tailTrace_2390312
  have hstable : (prefixWord ++ tailWord_2390312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390312).length < 2 ^ (prefixWord ++ tailWord_2390312).sum := by decide
  have hdescent : baseEnd_2390312 < baseStart_2390312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390351 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 6]
def baseStart_2390351 : Nat := 118140960795 + 2390351 * 2 ^ 59
def prefixEnd_2390351 : Nat := 4983230072969 + 3 ^ 40 * 2390351 * 2
def baseEnd_2390351 : Nat := 272755332434551660982107

theorem tailTrace_2390351 : CollatzResearch.WordTrace tailWord_2390351 prefixEnd_2390351 272755332434551660982107 := by
  unfold tailWord_2390351
  simp only [CollatzResearch.WordTrace]
  refine ⟨87183263363174041294306907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58122175575449360862871271 87183263363174041294306907)
  ·
    refine ⟨130774895044761061941460361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87183263363174041294306907 130774895044761061941460361)
    ·
      refine ⟨98081171283570796456095271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130774895044761061941460361 98081171283570796456095271)
      ·
        refine ⟨147121756925356194684142907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98081171283570796456095271 147121756925356194684142907)
        ·
          refine ⟨220682635388034292026214361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147121756925356194684142907 220682635388034292026214361)
          ·
            refine ⟨165511976541025719019660771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220682635388034292026214361 165511976541025719019660771)
            ·
              refine ⟨248267964811538578529491157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165511976541025719019660771 248267964811538578529491157)
              ·
                refine ⟨5818780425270435434284949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 248267964811538578529491157 5818780425270435434284949)
                ·
                  refine ⟨272755332434551660982107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5818780425270435434284949 272755332434551660982107)
                  ·
                    rfl

theorem cell22_2390351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 6].length) (baseStart_2390351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390351 prefixEnd_2390351 := by exact prefixLift 2390351
  have htrace : WordTrace (prefixWord ++ tailWord_2390351) baseStart_2390351 baseEnd_2390351 := by
    simpa [prefixWord, tailWord_2390351, baseEnd_2390351] using wordTrace_append hprefix tailTrace_2390351
  have hstable : (prefixWord ++ tailWord_2390351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390351).length < 2 ^ (prefixWord ++ tailWord_2390351).sum := by decide
  have hdescent : baseEnd_2390351 < baseStart_2390351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390357 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 5]
def baseStart_2390357 : Nat := 118140960795 + 2390357 * 2 ^ 59
def prefixEnd_2390357 : Nat := 4983230072969 + 3 ^ 40 * 2390357 * 2
def baseEnd_2390357 : Nat := 272756017075424322432101

theorem tailTrace_2390357 : CollatzResearch.WordTrace tailWord_2390357 prefixEnd_2390357 272756017075424322432101 := by
  unfold tailWord_2390357
  simp only [CollatzResearch.WordTrace]
  refine ⟨87183482201152304319025325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58122321467434869546016883 87183482201152304319025325)
  ·
    refine ⟨32693805825432114119634497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87183482201152304319025325 32693805825432114119634497)
    ·
      refine ⟨24520354369074085589725873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32693805825432114119634497 24520354369074085589725873)
      ·
        refine ⟨18390265776805564192294405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24520354369074085589725873 18390265776805564192294405)
        ·
          refine ⟨3448174833151043286055201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18390265776805564192294405 3448174833151043286055201)
          ·
            refine ⟨2586131124863282464541401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3448174833151043286055201 2586131124863282464541401)
            ·
              refine ⟨1939598343647461848406051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586131124863282464541401 1939598343647461848406051)
              ·
                refine ⟨2909397515471192772609077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939598343647461848406051 2909397515471192772609077)
                ·
                  refine ⟨272756017075424322432101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909397515471192772609077 272756017075424322432101)
                  ·
                    rfl

theorem cell22_2390357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_2390357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390357 prefixEnd_2390357 := by exact prefixLift 2390357
  have htrace : WordTrace (prefixWord ++ tailWord_2390357) baseStart_2390357 baseEnd_2390357 := by
    simpa [prefixWord, tailWord_2390357, baseEnd_2390357] using wordTrace_append hprefix tailTrace_2390357
  have hstable : (prefixWord ++ tailWord_2390357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390357).length < 2 ^ (prefixWord ++ tailWord_2390357).sum := by decide
  have hdescent : baseEnd_2390357 < baseStart_2390357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390370 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2390370 : Nat := 118140960795 + 2390370 * 2 ^ 59
def prefixEnd_2390370 : Nat := 4983230072969 + 3 ^ 40 * 2390370 * 2
def baseEnd_2390370 : Nat := 818272501391945266721263

theorem tailTrace_2390370 : CollatzResearch.WordTrace tailWord_2390370 prefixEnd_2390370 818272501391945266721263 := by
  unfold tailWord_2390370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795989087526301884812141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58122637566736805026165709 21795989087526301884812141)
  ·
    refine ⟨8173495907822363206804553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21795989087526301884812141 8173495907822363206804553)
    ·
      refine ⟨6130121930866772405103415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8173495907822363206804553 6130121930866772405103415)
      ·
        refine ⟨9195182896300158607655123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130121930866772405103415 9195182896300158607655123)
        ·
          refine ⟨13792774344450237911482685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195182896300158607655123 13792774344450237911482685)
          ·
            refine ⟨5172290379168839216806007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13792774344450237911482685 5172290379168839216806007)
            ·
              refine ⟨7758435568753258825209011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172290379168839216806007 7758435568753258825209011)
              ·
                refine ⟨11637653353129888237813517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7758435568753258825209011 11637653353129888237813517)
                ·
                  refine ⟨4364120007423708089180069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11637653353129888237813517 4364120007423708089180069)
                  ·
                    refine ⟨818272501391945266721263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4364120007423708089180069 818272501391945266721263)
                    ·
                      rfl

theorem cell22_2390370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2390370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390370 prefixEnd_2390370 := by exact prefixLift 2390370
  have htrace : WordTrace (prefixWord ++ tailWord_2390370) baseStart_2390370 baseEnd_2390370 := by
    simpa [prefixWord, tailWord_2390370, baseEnd_2390370] using wordTrace_append hprefix tailTrace_2390370
  have hstable : (prefixWord ++ tailWord_2390370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390370).length < 2 ^ (prefixWord ++ tailWord_2390370).sum := by decide
  have hdescent : baseEnd_2390370 < baseStart_2390370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390383 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 4, 3]
def baseStart_2390383 : Nat := 118140960795 + 2390383 * 2 ^ 59
def prefixEnd_2390383 : Nat := 4983230072969 + 3 ^ 40 * 2390383 * 2
def baseEnd_2390383 : Nat := 818276951557617566146223

theorem tailTrace_2390383 : CollatzResearch.WordTrace tailWord_2390383 prefixEnd_2390383 818276951557617566146223 := by
  unfold tailWord_2390383
  simp only [CollatzResearch.WordTrace]
  refine ⟨87184430499058110759471803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58122953666038740506314535 87184430499058110759471803)
  ·
    refine ⟨130776645748587166139207705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87184430499058110759471803 130776645748587166139207705)
    ·
      refine ⟨98082484311440374604405779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130776645748587166139207705 98082484311440374604405779)
      ·
        refine ⟨147123726467160561906608669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98082484311440374604405779 147123726467160561906608669)
        ·
          refine ⟨55171397425185210714978251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147123726467160561906608669 55171397425185210714978251)
          ·
            refine ⟨82757096137777816072467377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55171397425185210714978251 82757096137777816072467377)
            ·
              refine ⟨62067822103333362054350533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82757096137777816072467377 62067822103333362054350533)
              ·
                refine ⟨11637716644375005385190725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62067822103333362054350533 11637716644375005385190725)
                ·
                  refine ⟨2182071870820313509723261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11637716644375005385190725 2182071870820313509723261)
                  ·
                    refine ⟨818276951557617566146223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182071870820313509723261 818276951557617566146223)
                    ·
                      rfl

theorem cell22_2390383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_2390383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390383 prefixEnd_2390383 := by exact prefixLift 2390383
  have htrace : WordTrace (prefixWord ++ tailWord_2390383) baseStart_2390383 baseEnd_2390383 := by
    simpa [prefixWord, tailWord_2390383, baseEnd_2390383] using wordTrace_append hprefix tailTrace_2390383
  have hstable : (prefixWord ++ tailWord_2390383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390383).length < 2 ^ (prefixWord ++ tailWord_2390383).sum := by decide
  have hdescent : baseEnd_2390383 < baseStart_2390383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390473 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_2390473 : Nat := 118140960795 + 2390473 * 2 ^ 59
def prefixEnd_2390473 : Nat := 4983230072969 + 3 ^ 40 * 2390473 * 2
def baseEnd_2390473 : Nat := 818307760396887331395947

theorem tailTrace_2390473 : CollatzResearch.WordTrace tailWord_2390473 prefixEnd_2390473 818307760396887331395947 := by
  unfold tailWord_2390473
  simp only [CollatzResearch.WordTrace]
  refine ⟨87187713068732056130248073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58125142045821370753498715 87187713068732056130248073)
  ·
    refine ⟨65390784801549042097686055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87187713068732056130248073 65390784801549042097686055)
    ·
      refine ⟨98086177202323563146529083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65390784801549042097686055 98086177202323563146529083)
      ·
        refine ⟨147129265803485344719793625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98086177202323563146529083 147129265803485344719793625)
        ·
          refine ⟨110346949352614008539845219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147129265803485344719793625 110346949352614008539845219)
          ·
            refine ⟨165520424028921012809767829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110346949352614008539845219 165520424028921012809767829)
            ·
              refine ⟨7758769876355672475457867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165520424028921012809767829 7758769876355672475457867)
              ·
                refine ⟨11638154814533508713186801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7758769876355672475457867 11638154814533508713186801)
                ·
                  refine ⟨8728616110900131534890101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11638154814533508713186801 8728616110900131534890101)
                  ·
                    refine ⟨818307760396887331395947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8728616110900131534890101 818307760396887331395947)
                    ·
                      rfl

theorem cell22_2390473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_2390473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390473 prefixEnd_2390473 := by exact prefixLift 2390473
  have htrace : WordTrace (prefixWord ++ tailWord_2390473) baseStart_2390473 baseEnd_2390473 := by
    simpa [prefixWord, tailWord_2390473, baseEnd_2390473] using wordTrace_append hprefix tailTrace_2390473
  have hstable : (prefixWord ++ tailWord_2390473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390473).length < 2 ^ (prefixWord ++ tailWord_2390473).sum := by decide
  have hdescent : baseEnd_2390473 < baseStart_2390473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390533 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2390533 : Nat := 118140960795 + 2390533 * 2 ^ 59
def prefixEnd_2390533 : Nat := 4983230072969 + 3 ^ 40 * 2390533 * 2
def baseEnd_2390533 : Nat := 818328299623067174895763

theorem tailTrace_2390533 : CollatzResearch.WordTrace tailWord_2390533 prefixEnd_2390533 818328299623067174895763 := by
  unfold tailWord_2390533
  simp only [CollatzResearch.WordTrace]
  refine ⟨87189901448514686377432253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58126600965676457584954835 87189901448514686377432253)
  ·
    refine ⟨32696213043193007391537095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87189901448514686377432253 32696213043193007391537095)
    ·
      refine ⟨49044319564789511087305643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32696213043193007391537095 49044319564789511087305643)
      ·
        refine ⟨73566479347184266630958465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49044319564789511087305643 73566479347184266630958465)
        ·
          refine ⟨55174859510388199973218849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73566479347184266630958465 55174859510388199973218849)
          ·
            refine ⟨41381144632791149979914137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55174859510388199973218849 41381144632791149979914137)
            ·
              refine ⟨31035858474593362484935603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41381144632791149979914137 31035858474593362484935603)
              ·
                refine ⟨46553787711890043727403405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31035858474593362484935603 46553787711890043727403405)
                ·
                  refine ⟨17457670391958766397776277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46553787711890043727403405 17457670391958766397776277)
                  ·
                    refine ⟨818328299623067174895763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17457670391958766397776277 818328299623067174895763)
                    ·
                      rfl

theorem cell22_2390533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2390533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390533 prefixEnd_2390533 := by exact prefixLift 2390533
  have htrace : WordTrace (prefixWord ++ tailWord_2390533) baseStart_2390533 baseEnd_2390533 := by
    simpa [prefixWord, tailWord_2390533, baseEnd_2390533] using wordTrace_append hprefix tailTrace_2390533
  have hstable : (prefixWord ++ tailWord_2390533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390533).length < 2 ^ (prefixWord ++ tailWord_2390533).sum := by decide
  have hdescent : baseEnd_2390533 < baseStart_2390533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390582 : List Nat := [5, 1, 2, 1, 2, 1, 3, 7]
def baseStart_2390582 : Nat := 118140960795 + 2390582 * 2 ^ 59
def prefixEnd_2390582 : Nat := 4983230072969 + 3 ^ 40 * 2390582 * 2
def baseEnd_2390582 : Nat := 90927230369383042268957

theorem tailTrace_2390582 : CollatzResearch.WordTrace tailWord_2390582 prefixEnd_2390582 90927230369383042268957 := by
  unfold tailWord_2390582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449480539083572984122875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58127792416891445163977333 5449480539083572984122875)
  ·
    refine ⟨8174220808625359476184313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5449480539083572984122875 8174220808625359476184313)
    ·
      refine ⟨6130665606469019607138235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8174220808625359476184313 6130665606469019607138235)
      ·
        refine ⟨9195998409703529410707353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130665606469019607138235 9195998409703529410707353)
        ·
          refine ⟨6896998807277647058030515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9195998409703529410707353 6896998807277647058030515)
          ·
            refine ⟨10345498210916470587045773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6896998807277647058030515 10345498210916470587045773)
            ·
              refine ⟨3879561829093676470142165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10345498210916470587045773 3879561829093676470142165)
              ·
                refine ⟨90927230369383042268957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3879561829093676470142165 90927230369383042268957)
                ·
                  rfl

theorem cell22_2390582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_2390582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390582 prefixEnd_2390582 := by exact prefixLift 2390582
  have htrace : WordTrace (prefixWord ++ tailWord_2390582) baseStart_2390582 baseEnd_2390582 := by
    simpa [prefixWord, tailWord_2390582, baseEnd_2390582] using wordTrace_append hprefix tailTrace_2390582
  have hstable : (prefixWord ++ tailWord_2390582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390582).length < 2 ^ (prefixWord ++ tailWord_2390582).sum := by decide
  have hdescent : baseEnd_2390582 < baseStart_2390582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390597 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_2390597 : Nat := 118140960795 + 2390597 * 2 ^ 59
def prefixEnd_2390597 : Nat := 4983230072969 + 3 ^ 40 * 2390597 * 2
def baseEnd_2390597 : Nat := 818350208130992341295567

theorem tailTrace_2390597 : CollatzResearch.WordTrace tailWord_2390597 prefixEnd_2390597 818350208130992341295567 := by
  unfold tailWord_2390597
  simp only [CollatzResearch.WordTrace]
  refine ⟨87192235720282825307762045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58128157146855216871841363 87192235720282825307762045)
  ·
    refine ⟨32697088395106059490410767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87192235720282825307762045 32697088395106059490410767)
    ·
      refine ⟨49045632592659089235616151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32697088395106059490410767 49045632592659089235616151)
      ·
        refine ⟨73568448888988633853424227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49045632592659089235616151 73568448888988633853424227)
        ·
          refine ⟨110352673333482950780136341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73568448888988633853424227 110352673333482950780136341)
          ·
            refine ⟨5172781562507013317818891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110352673333482950780136341 5172781562507013317818891)
            ·
              refine ⟨7759172343760519976728337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172781562507013317818891 7759172343760519976728337)
              ·
                refine ⟨5819379257820389982546253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7759172343760519976728337 5819379257820389982546253)
                ·
                  refine ⟨2182267221682646243454845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5819379257820389982546253 2182267221682646243454845)
                  ·
                    refine ⟨818350208130992341295567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182267221682646243454845 818350208130992341295567)
                    ·
                      rfl

theorem cell22_2390597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_2390597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390597 prefixEnd_2390597 := by exact prefixLift 2390597
  have htrace : WordTrace (prefixWord ++ tailWord_2390597) baseStart_2390597 baseEnd_2390597 := by
    simpa [prefixWord, tailWord_2390597, baseEnd_2390597] using wordTrace_append hprefix tailTrace_2390597
  have hstable : (prefixWord ++ tailWord_2390597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390597).length < 2 ^ (prefixWord ++ tailWord_2390597).sum := by decide
  have hdescent : baseEnd_2390597 < baseStart_2390597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390610 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_2390610 : Nat := 118140960795 + 2390610 * 2 ^ 59
def prefixEnd_2390610 : Nat := 4983230072969 + 3 ^ 40 * 2390610 * 2
def baseEnd_2390610 : Nat := 272784886098888213573509

theorem tailTrace_2390610 : CollatzResearch.WordTrace tailWord_2390610 prefixEnd_2390610 272784886098888213573509 := by
  unfold tailWord_2390610
  simp only [CollatzResearch.WordTrace]
  refine ⟨21798177467308932131996321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58128473246157152351990189 21798177467308932131996321)
  ·
    refine ⟨16348633100481699098997241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21798177467308932131996321 16348633100481699098997241)
    ·
      refine ⟨12261474825361274324247931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16348633100481699098997241 12261474825361274324247931)
      ·
        refine ⟨18392212238041911486371897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12261474825361274324247931 18392212238041911486371897)
        ·
          refine ⟨13794159178531433614778923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18392212238041911486371897 13794159178531433614778923)
          ·
            refine ⟨20691238767797150422168385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13794159178531433614778923 20691238767797150422168385)
            ·
              refine ⟨15518429075847862816626289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20691238767797150422168385 15518429075847862816626289)
              ·
                refine ⟨11638821806885897112469717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15518429075847862816626289 11638821806885897112469717)
                ·
                  refine ⟨272784886098888213573509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11638821806885897112469717 272784886098888213573509)
                  ·
                    rfl

theorem cell22_2390610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_2390610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390610 prefixEnd_2390610 := by exact prefixLift 2390610
  have htrace : WordTrace (prefixWord ++ tailWord_2390610) baseStart_2390610 baseEnd_2390610 := by
    simpa [prefixWord, tailWord_2390610, baseEnd_2390610] using wordTrace_append hprefix tailTrace_2390610
  have hstable : (prefixWord ++ tailWord_2390610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390610).length < 2 ^ (prefixWord ++ tailWord_2390610).sum := by decide
  have hdescent : baseEnd_2390610 < baseStart_2390610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390625 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2390625 : Nat := 118140960795 + 2390625 * 2 ^ 59
def prefixEnd_2390625 : Nat := 4983230072969 + 3 ^ 40 * 2390625 * 2
def baseEnd_2390625 : Nat := 818359793103209601595481

theorem tailTrace_2390625 : CollatzResearch.WordTrace tailWord_2390625 prefixEnd_2390625 818359793103209601595481 := by
  unfold tailWord_2390625
  simp only [CollatzResearch.WordTrace]
  refine ⟨87193256964181386089781329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58128837976120924059854219 87193256964181386089781329)
  ·
    refine ⟨65394942723136039567335997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87193256964181386089781329 65394942723136039567335997)
    ·
      refine ⟨24523103521176014837750999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65394942723136039567335997 24523103521176014837750999)
      ·
        refine ⟨36784655281764022256626499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24523103521176014837750999 36784655281764022256626499)
        ·
          refine ⟨55176982922646033384939749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36784655281764022256626499 55176982922646033384939749)
          ·
            refine ⟨10345684297996131259676203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55176982922646033384939749 10345684297996131259676203)
            ·
              refine ⟨15518526446994196889514305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10345684297996131259676203 15518526446994196889514305)
              ·
                refine ⟨11638894835245647667135729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15518526446994196889514305 11638894835245647667135729)
                ·
                  refine ⟨8729171126434235750351797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11638894835245647667135729 8729171126434235750351797)
                  ·
                    refine ⟨818359793103209601595481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8729171126434235750351797 818359793103209601595481)
                    ·
                      rfl

theorem cell22_2390625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2390625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390625 prefixEnd_2390625 := by exact prefixLift 2390625
  have htrace : WordTrace (prefixWord ++ tailWord_2390625) baseStart_2390625 baseEnd_2390625 := by
    simpa [prefixWord, tailWord_2390625, baseEnd_2390625] using wordTrace_append hprefix tailTrace_2390625
  have hstable : (prefixWord ++ tailWord_2390625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390625).length < 2 ^ (prefixWord ++ tailWord_2390625).sum := by decide
  have hdescent : baseEnd_2390625 < baseStart_2390625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390674 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2390674 : Nat := 118140960795 + 2390674 * 2 ^ 59
def prefixEnd_2390674 : Nat := 4983230072969 + 3 ^ 40 * 2390674 * 2
def baseEnd_2390674 : Nat := 818376566804589807120331

theorem tailTrace_2390674 : CollatzResearch.WordTrace tailWord_2390674 prefixEnd_2390674 818376566804589807120331 := by
  unfold tailWord_2390674
  simp only [CollatzResearch.WordTrace]
  refine ⟨21798761035250966864578769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58130029427335911638876717 21798761035250966864578769)
  ·
    refine ⟨16349070776438225148434077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21798761035250966864578769 16349070776438225148434077)
    ·
      refine ⟨6130901541164334430662779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16349070776438225148434077 6130901541164334430662779)
      ·
        refine ⟨9196352311746501645994169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130901541164334430662779 9196352311746501645994169)
        ·
          refine ⟨6897264233809876234495627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9196352311746501645994169 6897264233809876234495627)
          ·
            refine ⟨10345896350714814351743441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897264233809876234495627 10345896350714814351743441)
            ·
              refine ⟨7759422263036110763807581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10345896350714814351743441 7759422263036110763807581)
              ·
                refine ⟨2909783348638541536427843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7759422263036110763807581 2909783348638541536427843)
                ·
                  refine ⟨4364675022957812304641765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909783348638541536427843 4364675022957812304641765)
                  ·
                    refine ⟨818376566804589807120331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4364675022957812304641765 818376566804589807120331)
                    ·
                      rfl

theorem cell22_2390674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2390674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390674 prefixEnd_2390674 := by exact prefixLift 2390674
  have htrace : WordTrace (prefixWord ++ tailWord_2390674) baseStart_2390674 baseEnd_2390674 := by
    simpa [prefixWord, tailWord_2390674, baseEnd_2390674] using wordTrace_append hprefix tailTrace_2390674
  have hstable : (prefixWord ++ tailWord_2390674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390674).length < 2 ^ (prefixWord ++ tailWord_2390674).sum := by decide
  have hdescent : baseEnd_2390674 < baseStart_2390674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390689 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 6]
def baseStart_2390689 : Nat := 118140960795 + 2390689 * 2 ^ 59
def prefixEnd_2390689 : Nat := 4983230072969 + 3 ^ 40 * 2390689 * 2
def baseEnd_2390689 : Nat := 272793900537044922665095

theorem tailTrace_2390689 : CollatzResearch.WordTrace tailWord_2390689 prefixEnd_2390689 272793900537044922665095 := by
  unfold tailWord_2390689
  simp only [CollatzResearch.WordTrace]
  refine ⟨87195591235949525020111121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58130394157299683346740747 87195591235949525020111121)
  ·
    refine ⟨65396693426962143765083341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87195591235949525020111121 65396693426962143765083341)
    ·
      refine ⟨24523760035110803911906253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65396693426962143765083341 24523760035110803911906253)
      ·
        refine ⟨9196410013166551466964845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24523760035110803911906253 9196410013166551466964845)
        ·
          refine ⟨3448653754937456800111817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9196410013166551466964845 3448653754937456800111817)
          ·
            refine ⟨2586490316203092600083863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3448653754937456800111817 2586490316203092600083863)
            ·
              refine ⟨3879735474304638900125795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586490316203092600083863 3879735474304638900125795)
              ·
                refine ⟨5819603211456958350188693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879735474304638900125795 5819603211456958350188693)
                ·
                  refine ⟨272793900537044922665095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5819603211456958350188693 272793900537044922665095)
                  ·
                    rfl

theorem cell22_2390689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_2390689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390689 prefixEnd_2390689 := by exact prefixLift 2390689
  have htrace : WordTrace (prefixWord ++ tailWord_2390689) baseStart_2390689 baseEnd_2390689 := by
    simpa [prefixWord, tailWord_2390689, baseEnd_2390689] using wordTrace_append hprefix tailTrace_2390689
  have hstable : (prefixWord ++ tailWord_2390689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390689).length < 2 ^ (prefixWord ++ tailWord_2390689).sum := by decide
  have hdescent : baseEnd_2390689 < baseStart_2390689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390721 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2390721 : Nat := 118140960795 + 2390721 * 2 ^ 59
def prefixEnd_2390721 : Nat := 4983230072969 + 3 ^ 40 * 2390721 * 2
def baseEnd_2390721 : Nat := 818392655865097351195187

theorem tailTrace_2390721 : CollatzResearch.WordTrace tailWord_2390721 prefixEnd_2390721 818392655865097351195187 := by
  unfold tailWord_2390721
  simp only [CollatzResearch.WordTrace]
  refine ⟨87196758371833594485276017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58131172247889062990184011 87196758371833594485276017)
  ·
    refine ⟨65397568778875195863957013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87196758371833594485276017 65397568778875195863957013)
    ·
      refine ⟨3065511036509774806122985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65397568778875195863957013 3065511036509774806122985)
      ·
        refine ⟨2299133277382331104592239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3065511036509774806122985 2299133277382331104592239)
        ·
          refine ⟨3448699916073496656888359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299133277382331104592239 3448699916073496656888359)
          ·
            refine ⟨5173049874110244985332539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448699916073496656888359 5173049874110244985332539)
            ·
              refine ⟨7759574811165367477998809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173049874110244985332539 7759574811165367477998809)
              ·
                refine ⟨5819681108374025608499107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7759574811165367477998809 5819681108374025608499107)
                ·
                  refine ⟨8729521662561038412748661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5819681108374025608499107 8729521662561038412748661)
                  ·
                    refine ⟨818392655865097351195187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8729521662561038412748661 818392655865097351195187)
                    ·
                      rfl

theorem cell22_2390721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2390721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390721 prefixEnd_2390721 := by exact prefixLift 2390721
  have htrace : WordTrace (prefixWord ++ tailWord_2390721) baseStart_2390721 baseEnd_2390721 := by
    simpa [prefixWord, tailWord_2390721, baseEnd_2390721] using wordTrace_append hprefix tailTrace_2390721
  have hstable : (prefixWord ++ tailWord_2390721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390721).length < 2 ^ (prefixWord ++ tailWord_2390721).sum := by decide
  have hdescent : baseEnd_2390721 < baseStart_2390721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390740 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2390740 : Nat := 118140960795 + 2390740 * 2 ^ 59
def prefixEnd_2390740 : Nat := 4983230072969 + 3 ^ 40 * 2390740 * 2
def baseEnd_2390740 : Nat := 272799719984462544990043

theorem tailTrace_2390740 : CollatzResearch.WordTrace tailWord_2390740 prefixEnd_2390740 272799719984462544990043 := by
  unfold tailWord_2390740
  simp only [CollatzResearch.WordTrace]
  refine ⟨43598725679382380365108837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58131634239176507153478449 43598725679382380365108837)
  ·
    refine ⟨8174761064884196318457907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43598725679382380365108837 8174761064884196318457907)
    ·
      refine ⟨12262141597326294477686861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8174761064884196318457907 12262141597326294477686861)
      ·
        refine ⟨4598303098997360429132573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12262141597326294477686861 4598303098997360429132573)
        ·
          refine ⟨1724363662124010160924715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4598303098997360429132573 1724363662124010160924715)
          ·
            refine ⟨2586545493186015241387073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724363662124010160924715 2586545493186015241387073)
            ·
              refine ⟨1939909119889511431040305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586545493186015241387073 1939909119889511431040305)
              ·
                refine ⟨1454931839917133573280229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1939909119889511431040305 1454931839917133573280229)
                ·
                  refine ⟨272799719984462544990043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454931839917133573280229 272799719984462544990043)
                  ·
                    rfl

theorem cell22_2390740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2390740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390740 prefixEnd_2390740 := by exact prefixLift 2390740
  have htrace : WordTrace (prefixWord ++ tailWord_2390740) baseStart_2390740 baseEnd_2390740 := by
    simpa [prefixWord, tailWord_2390740, baseEnd_2390740] using wordTrace_append hprefix tailTrace_2390740
  have hstable : (prefixWord ++ tailWord_2390740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390740).length < 2 ^ (prefixWord ++ tailWord_2390740).sum := by decide
  have hdescent : baseEnd_2390740 < baseStart_2390740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390813 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 5]
def baseStart_2390813 : Nat := 118140960795 + 2390813 * 2 ^ 59
def prefixEnd_2390813 : Nat := 4983230072969 + 3 ^ 40 * 2390813 * 2
def baseEnd_2390813 : Nat := 272808049781746592631635

theorem tailTrace_2390813 : CollatzResearch.WordTrace tailWord_2390813 prefixEnd_2390813 272808049781746592631635 := by
  unfold tailWord_2390813
  simp only [CollatzResearch.WordTrace]
  refine ⟨87200113887500294197625093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58133409258333529465083395 87200113887500294197625093)
  ·
    refine ⟨16350021353906305162054705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87200113887500294197625093 16350021353906305162054705)
    ·
      refine ⟨12262516015429728871541029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16350021353906305162054705 12262516015429728871541029)
      ·
        refine ⟨2299221752893074163413943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12262516015429728871541029 2299221752893074163413943)
        ·
          refine ⟨3448832629339611245120915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299221752893074163413943 3448832629339611245120915)
          ·
            refine ⟨5173248944009416867681373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448832629339611245120915 5173248944009416867681373)
            ·
              refine ⟨1939968354003531325380515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5173248944009416867681373 1939968354003531325380515)
              ·
                refine ⟨2909952531005296988070773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939968354003531325380515 2909952531005296988070773)
                ·
                  refine ⟨272808049781746592631635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909952531005296988070773 272808049781746592631635)
                  ·
                    rfl

theorem cell22_2390813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_2390813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390813 prefixEnd_2390813 := by exact prefixLift 2390813
  have htrace : WordTrace (prefixWord ++ tailWord_2390813) baseStart_2390813 baseEnd_2390813 := by
    simpa [prefixWord, tailWord_2390813, baseEnd_2390813] using wordTrace_append hprefix tailTrace_2390813
  have hstable : (prefixWord ++ tailWord_2390813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390813).length < 2 ^ (prefixWord ++ tailWord_2390813).sum := by decide
  have hdescent : baseEnd_2390813 < baseStart_2390813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390873 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 2, 3]
def baseStart_2390873 : Nat := 118140960795 + 2390873 * 2 ^ 59
def prefixEnd_2390873 : Nat := 4983230072969 + 3 ^ 40 * 2390873 * 2
def baseEnd_2390873 : Nat := 818444688571419621394721

theorem tailTrace_2390873 : CollatzResearch.WordTrace tailWord_2390873 prefixEnd_2390873 818444688571419621394721 := by
  unfold tailWord_2390873
  simp only [CollatzResearch.WordTrace]
  refine ⟨87202302267282924444809273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58134868178188616296539515 87202302267282924444809273)
  ·
    refine ⟨65401726700462193333606955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87202302267282924444809273 65401726700462193333606955)
    ·
      refine ⟨98102590050693290000410433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65401726700462193333606955 98102590050693290000410433)
      ·
        refine ⟨73576942538019967500307825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98102590050693290000410433 73576942538019967500307825)
        ·
          refine ⟨55182706903514975625230869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73576942538019967500307825 55182706903514975625230869)
          ·
            refine ⟨2586689386102264482432697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55182706903514975625230869 2586689386102264482432697)
            ·
              refine ⟨1940017039576698361824523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586689386102264482432697 1940017039576698361824523)
              ·
                refine ⟨2910025559365047542736785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940017039576698361824523 2910025559365047542736785)
                ·
                  refine ⟨2182519169523785657052589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910025559365047542736785 2182519169523785657052589)
                  ·
                    refine ⟨818444688571419621394721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182519169523785657052589 818444688571419621394721)
                    ·
                      rfl

theorem cell22_2390873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_2390873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390873 prefixEnd_2390873 := by exact prefixLift 2390873
  have htrace : WordTrace (prefixWord ++ tailWord_2390873) baseStart_2390873 baseEnd_2390873 := by
    simpa [prefixWord, tailWord_2390873, baseEnd_2390873] using wordTrace_append hprefix tailTrace_2390873
  have hstable : (prefixWord ++ tailWord_2390873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390873).length < 2 ^ (prefixWord ++ tailWord_2390873).sum := by decide
  have hdescent : baseEnd_2390873 < baseStart_2390873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390944 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_2390944 : Nat := 118140960795 + 2390944 * 2 ^ 59
def prefixEnd_2390944 : Nat := 4983230072969 + 3 ^ 40 * 2390944 * 2
def baseEnd_2390944 : Nat := 818468993322399102869503

theorem tailTrace_2390944 : CollatzResearch.WordTrace tailWord_2390944 prefixEnd_2390944 818468993322399102869503 := by
  unfold tailWord_2390944
  simp only [CollatzResearch.WordTrace]
  refine ⟨43602445925012851785321943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58136594566683802380429257 43602445925012851785321943)
  ·
    refine ⟨65403668887519277677982915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43602445925012851785321943 65403668887519277677982915)
    ·
      refine ⟨98105503331278916516974373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65403668887519277677982915 98105503331278916516974373)
      ·
        refine ⟨18394781874614796846932695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98105503331278916516974373 18394781874614796846932695)
        ·
          refine ⟨27592172811922195270399043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18394781874614796846932695 27592172811922195270399043)
          ·
            refine ⟨41388259217883292905598565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27592172811922195270399043 41388259217883292905598565)
            ·
              refine ⟨7760298603353117419799731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41388259217883292905598565 7760298603353117419799731)
              ·
                refine ⟨11640447905029676129699597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760298603353117419799731 11640447905029676129699597)
                ·
                  refine ⟨4365167964386128548637349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11640447905029676129699597 4365167964386128548637349)
                  ·
                    refine ⟨818468993322399102869503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4365167964386128548637349 818468993322399102869503)
                    ·
                      rfl

theorem cell22_2390944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_2390944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390944 prefixEnd_2390944 := by exact prefixLift 2390944
  have htrace : WordTrace (prefixWord ++ tailWord_2390944) baseStart_2390944 baseEnd_2390944 := by
    simpa [prefixWord, tailWord_2390944, baseEnd_2390944] using wordTrace_append hprefix tailTrace_2390944
  have hstable : (prefixWord ++ tailWord_2390944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390944).length < 2 ^ (prefixWord ++ tailWord_2390944).sum := by decide
  have hdescent : baseEnd_2390944 < baseStart_2390944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390976 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 4]
def baseStart_2390976 : Nat := 118140960795 + 2390976 * 2 ^ 59
def prefixEnd_2390976 : Nat := 4983230072969 + 3 ^ 40 * 2390976 * 2
def baseEnd_2390976 : Nat := 272826649192120562023135

theorem tailTrace_2390976 : CollatzResearch.WordTrace tailWord_2390976 prefixEnd_2390976 272826649192120562023135 := by
  unfold tailWord_2390976
  simp only [CollatzResearch.WordTrace]
  refine ⟨43603029492954886517904391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58137372657273182023872521 43603029492954886517904391)
  ·
    refine ⟨65404544239432329776856587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43603029492954886517904391 65404544239432329776856587)
    ·
      refine ⟨98106816359148494665284881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65404544239432329776856587 98106816359148494665284881)
      ·
        refine ⟨73580112269361370998963661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98106816359148494665284881 73580112269361370998963661)
        ·
          refine ⟨27592542101010514124611373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73580112269361370998963661 27592542101010514124611373)
          ·
            refine ⟨10347203287878942796729265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27592542101010514124611373 10347203287878942796729265)
            ·
              refine ⟨7760402465909207097546949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10347203287878942796729265 7760402465909207097546949)
              ·
                refine ⟨1455075462357976330790053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7760402465909207097546949 1455075462357976330790053)
                ·
                  refine ⟨272826649192120562023135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455075462357976330790053 272826649192120562023135)
                  ·
                    rfl

theorem cell22_2390976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_2390976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390976 prefixEnd_2390976 := by exact prefixLift 2390976
  have htrace : WordTrace (prefixWord ++ tailWord_2390976) baseStart_2390976 baseEnd_2390976 := by
    simpa [prefixWord, tailWord_2390976, baseEnd_2390976] using wordTrace_append hprefix tailTrace_2390976
  have hstable : (prefixWord ++ tailWord_2390976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390976).length < 2 ^ (prefixWord ++ tailWord_2390976).sum := by decide
  have hdescent : baseEnd_2390976 < baseStart_2390976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390991 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 1, 5]
def baseStart_2390991 : Nat := 118140960795 + 2390991 * 2 ^ 59
def prefixEnd_2390991 : Nat := 4983230072969 + 3 ^ 40 * 2390991 * 2
def baseEnd_2390991 : Nat := 818485082382906646944359

theorem tailTrace_2390991 : CollatzResearch.WordTrace tailWord_2390991 prefixEnd_2390991 818485082382906646944359 := by
  unfold tailWord_2390991
  simp only [CollatzResearch.WordTrace]
  refine ⟨87206606080855430597604827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58137737387236953731736551 87206606080855430597604827)
  ·
    refine ⟨130809909121283145896407241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87206606080855430597604827 130809909121283145896407241)
    ·
      refine ⟨98107431840962359422305431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130809909121283145896407241 98107431840962359422305431)
      ·
        refine ⟨147161147761443539133458147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98107431840962359422305431 147161147761443539133458147)
        ·
          refine ⟨220741721642165308700187221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147161147761443539133458147 220741721642165308700187221)
          ·
            refine ⟨2586817050494124711330319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 220741721642165308700187221 2586817050494124711330319)
            ·
              refine ⟨3880225575741187066995479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586817050494124711330319 3880225575741187066995479)
              ·
                refine ⟨5820338363611780600493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880225575741187066995479 5820338363611780600493219)
                ·
                  refine ⟨8730507545417670900739829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5820338363611780600493219 8730507545417670900739829)
                  ·
                    refine ⟨818485082382906646944359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8730507545417670900739829 818485082382906646944359)
                    ·
                      rfl

theorem cell22_2390991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_2390991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2390991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2390991 prefixEnd_2390991 := by exact prefixLift 2390991
  have htrace : WordTrace (prefixWord ++ tailWord_2390991) baseStart_2390991 baseEnd_2390991 := by
    simpa [prefixWord, tailWord_2390991, baseEnd_2390991] using wordTrace_append hprefix tailTrace_2390991
  have hstable : (prefixWord ++ tailWord_2390991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390991).length < 2 ^ (prefixWord ++ tailWord_2390991).sum := by decide
  have hdescent : baseEnd_2390991 < baseStart_2390991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391010 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2391010 : Nat := 118140960795 + 2391010 * 2 ^ 59
def prefixEnd_2391010 : Nat := 4983230072969 + 3 ^ 40 * 2391010 * 2
def baseEnd_2391010 : Nat := 272830528823732310239767

theorem tailTrace_2391010 : CollatzResearch.WordTrace tailWord_2391010 prefixEnd_2391010 272830528823732310239767 := by
  unfold tailWord_2391010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801824766946649210636621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58138199378524397895030989 21801824766946649210636621)
  ·
    refine ⟨8175684287604993453988733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21801824766946649210636621 8175684287604993453988733)
    ·
      refine ⟨3065881607851872545245775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8175684287604993453988733 3065881607851872545245775)
      ·
        refine ⟨4598822411777808817868663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065881607851872545245775 4598822411777808817868663)
        ·
          refine ⟨6898233617666713226802995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598822411777808817868663 6898233617666713226802995)
          ·
            refine ⟨10347350426500069840204493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898233617666713226802995 10347350426500069840204493)
            ·
              refine ⟨3880256409937526190076685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10347350426500069840204493 3880256409937526190076685)
              ·
                refine ⟨1455096153726572321278757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3880256409937526190076685 1455096153726572321278757)
                ·
                  refine ⟨272830528823732310239767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455096153726572321278757 272830528823732310239767)
                  ·
                    rfl

theorem cell22_2391010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2391010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391010 prefixEnd_2391010 := by exact prefixLift 2391010
  have htrace : WordTrace (prefixWord ++ tailWord_2391010) baseStart_2391010 baseEnd_2391010 := by
    simpa [prefixWord, tailWord_2391010, baseEnd_2391010] using wordTrace_append hprefix tailTrace_2391010
  have hstable : (prefixWord ++ tailWord_2391010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391010).length < 2 ^ (prefixWord ++ tailWord_2391010).sum := by decide
  have hdescent : baseEnd_2391010 < baseStart_2391010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391038 : List Nat := [4, 2, 2, 2, 2, 1, 2, 7]
def baseStart_2391038 : Nat := 118140960795 + 2391038 * 2 ^ 59
def prefixEnd_2391038 : Nat := 4983230072969 + 3 ^ 40 * 2391038 * 2
def baseEnd_2391038 : Nat := 90944574604823799002135

theorem tailTrace_2391038 : CollatzResearch.WordTrace tailWord_2391038 prefixEnd_2391038 90944574604823799002135 := by
  unfold tailWord_2391038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901040038960644703070721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58138880207790105083043845 10901040038960644703070721)
  ·
    refine ⟨8175780029220483527303041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10901040038960644703070721 8175780029220483527303041)
    ·
      refine ⟨6131835021915362645477281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8175780029220483527303041 6131835021915362645477281)
      ·
        refine ⟨4598876266436521984107961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6131835021915362645477281 4598876266436521984107961)
        ·
          refine ⟨3449157199827391488080971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598876266436521984107961 3449157199827391488080971)
          ·
            refine ⟨5173735799741087232121457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449157199827391488080971 5173735799741087232121457)
            ·
              refine ⟨3880301849805815424091093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5173735799741087232121457 3880301849805815424091093)
              ·
                refine ⟨90944574604823799002135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3880301849805815424091093 90944574604823799002135)
                ·
                  rfl

theorem cell22_2391038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_2391038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391038 prefixEnd_2391038 := by exact prefixLift 2391038
  have htrace : WordTrace (prefixWord ++ tailWord_2391038) baseStart_2391038 baseEnd_2391038 := by
    simpa [prefixWord, tailWord_2391038, baseEnd_2391038] using wordTrace_append hprefix tailTrace_2391038
  have hstable : (prefixWord ++ tailWord_2391038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391038).length < 2 ^ (prefixWord ++ tailWord_2391038).sum := by decide
  have hdescent : baseEnd_2391038 < baseStart_2391038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391042 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2391042 : Nat := 118140960795 + 2391042 * 2 ^ 59
def prefixEnd_2391042 : Nat := 4983230072969 + 3 ^ 40 * 2391042 * 2
def baseEnd_2391042 : Nat := 818502540725159513919203

theorem tailTrace_2391042 : CollatzResearch.WordTrace tailWord_2391042 prefixEnd_2391042 818502540725159513919203 := by
  unfold tailWord_2391042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802116550917666576927845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58138977469113777538474253 21802116550917666576927845)
  ·
    refine ⟨4087896853297062483173971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21802116550917666576927845 4087896853297062483173971)
    ·
      refine ⟨6131845279945593724760957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4087896853297062483173971 6131845279945593724760957)
      ·
        refine ⟨2299441979979597646785359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6131845279945593724760957 2299441979979597646785359)
        ·
          refine ⟨3449162969969396470178039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299441979979597646785359 3449162969969396470178039)
          ·
            refine ⟨5173744454954094705267059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449162969969396470178039 5173744454954094705267059)
            ·
              refine ⟨7760616682431142057900589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173744454954094705267059 7760616682431142057900589)
              ·
                refine ⟨2910231255911678271712721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7760616682431142057900589 2910231255911678271712721)
                ·
                  refine ⟨2182673441933758703784541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910231255911678271712721 2182673441933758703784541)
                  ·
                    refine ⟨818502540725159513919203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182673441933758703784541 818502540725159513919203)
                    ·
                      rfl

theorem cell22_2391042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2391042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391042 prefixEnd_2391042 := by exact prefixLift 2391042
  have htrace : WordTrace (prefixWord ++ tailWord_2391042) baseStart_2391042 baseEnd_2391042 := by
    simpa [prefixWord, tailWord_2391042, baseEnd_2391042] using wordTrace_append hprefix tailTrace_2391042
  have hstable : (prefixWord ++ tailWord_2391042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391042).length < 2 ^ (prefixWord ++ tailWord_2391042).sum := by decide
  have hdescent : baseEnd_2391042 < baseStart_2391042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391096 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_2391096 : Nat := 118140960795 + 2391096 * 2 ^ 59
def prefixEnd_2391096 : Nat := 4983230072969 + 3 ^ 40 * 2391096 * 2
def baseEnd_2391096 : Nat := 818521026028721373069037

theorem tailTrace_2391096 : CollatzResearch.WordTrace tailWord_2391096 prefixEnd_2391096 818521026028721373069037 := by
  unfold tailWord_2391096
  simp only [CollatzResearch.WordTrace]
  refine ⟨43605217872737516765088571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58140290496983355686784761 43605217872737516765088571)
  ·
    refine ⟨65407826809106275147632857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43605217872737516765088571 65407826809106275147632857)
    ·
      refine ⟨49055870106829706360724643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65407826809106275147632857 49055870106829706360724643)
      ·
        refine ⟨73583805160244559541086965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49055870106829706360724643 73583805160244559541086965)
        ·
          refine ⟨6898481733772927456976903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73583805160244559541086965 6898481733772927456976903)
          ·
            refine ⟨10347722600659391185465355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898481733772927456976903 10347722600659391185465355)
            ·
              refine ⟨15521583900989086778198033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10347722600659391185465355 15521583900989086778198033)
              ·
                refine ⟨11641187925741815083648525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15521583900989086778198033 11641187925741815083648525)
                ·
                  refine ⟨4365445472153180656368197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11641187925741815083648525 4365445472153180656368197)
                  ·
                    refine ⟨818521026028721373069037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4365445472153180656368197 818521026028721373069037)
                    ·
                      rfl

theorem cell22_2391096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_2391096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391096 prefixEnd_2391096 := by exact prefixLift 2391096
  have htrace : WordTrace (prefixWord ++ tailWord_2391096) baseStart_2391096 baseEnd_2391096 := by
    simpa [prefixWord, tailWord_2391096, baseEnd_2391096] using wordTrace_append hprefix tailTrace_2391096
  have hstable : (prefixWord ++ tailWord_2391096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391096).length < 2 ^ (prefixWord ++ tailWord_2391096).sum := by decide
  have hdescent : baseEnd_2391096 < baseStart_2391096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391111 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 6]
def baseStart_2391111 : Nat := 118140960795 + 2391111 * 2 ^ 59
def prefixEnd_2391111 : Nat := 4983230072969 + 3 ^ 40 * 2391111 * 2
def baseEnd_2391111 : Nat := 272842053611755444647997

theorem tailTrace_2391111 : CollatzResearch.WordTrace tailWord_2391111 prefixEnd_2391111 272842053611755444647997 := by
  unfold tailWord_2391111
  simp only [CollatzResearch.WordTrace]
  refine ⟨87210982840420691091973187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58140655226947127394648791 87210982840420691091973187)
  ·
    refine ⟨130816474260631036637959781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87210982840420691091973187 130816474260631036637959781)
    ·
      refine ⟨24528088923868319369617459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130816474260631036637959781 24528088923868319369617459)
      ·
        refine ⟨36792133385802479054426189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24528088923868319369617459 36792133385802479054426189)
        ·
          refine ⟨13797050019675929645409821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36792133385802479054426189 13797050019675929645409821)
          ·
            refine ⟨5173893757378473617028683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13797050019675929645409821 5173893757378473617028683)
            ·
              refine ⟨7760840636067710425543025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173893757378473617028683 7760840636067710425543025)
              ·
                refine ⟨5820630477050782819157269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7760840636067710425543025 5820630477050782819157269)
                ·
                  refine ⟨272842053611755444647997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5820630477050782819157269 272842053611755444647997)
                  ·
                    rfl

theorem cell22_2391111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 6].length) (baseStart_2391111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391111 prefixEnd_2391111 := by exact prefixLift 2391111
  have htrace : WordTrace (prefixWord ++ tailWord_2391111) baseStart_2391111 baseEnd_2391111 := by
    simpa [prefixWord, tailWord_2391111, baseEnd_2391111] using wordTrace_append hprefix tailTrace_2391111
  have hstable : (prefixWord ++ tailWord_2391111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391111).length < 2 ^ (prefixWord ++ tailWord_2391111).sum := by decide
  have hdescent : baseEnd_2391111 < baseStart_2391111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391128 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 4]
def baseStart_2391128 : Nat := 118140960795 + 2391128 * 2 ^ 59
def prefixEnd_2391128 : Nat := 4983230072969 + 3 ^ 40 * 2391128 * 2
def baseEnd_2391128 : Nat := 272843993427561318756313

theorem tailTrace_2391128 : CollatzResearch.WordTrace tailWord_2391128 prefixEnd_2391128 272843993427561318756313 := by
  unfold tailWord_2391128
  simp only [CollatzResearch.WordTrace]
  refine ⟨43605801440679551497671019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58141068587572735330228025 43605801440679551497671019)
  ·
    refine ⟨65408702161019327246506529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43605801440679551497671019 65408702161019327246506529)
    ·
      refine ⟨49056526620764495434879897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65408702161019327246506529 49056526620764495434879897)
      ·
        refine ⟨36792394965573371576159923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49056526620764495434879897 36792394965573371576159923)
        ·
          refine ⟨55188592448360057364239885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36792394965573371576159923 55188592448360057364239885)
          ·
            refine ⟨20695722168135021511589957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55188592448360057364239885 20695722168135021511589957)
            ·
              refine ⟨3880447906525316533423117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20695722168135021511589957 3880447906525316533423117)
              ·
                refine ⟨1455167964946993700033669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3880447906525316533423117 1455167964946993700033669)
                ·
                  refine ⟨272843993427561318756313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455167964946993700033669 272843993427561318756313)
                  ·
                    rfl

theorem cell22_2391128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_2391128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391128 prefixEnd_2391128 := by exact prefixLift 2391128
  have htrace : WordTrace (prefixWord ++ tailWord_2391128) baseStart_2391128 baseEnd_2391128 := by
    simpa [prefixWord, tailWord_2391128, baseEnd_2391128] using wordTrace_append hprefix tailTrace_2391128
  have hstable : (prefixWord ++ tailWord_2391128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391128).length < 2 ^ (prefixWord ++ tailWord_2391128).sum := by decide
  have hdescent : baseEnd_2391128 < baseStart_2391128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391141 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_2391141 : Nat := 118140960795 + 2391141 * 2 ^ 59
def prefixEnd_2391141 : Nat := 4983230072969 + 3 ^ 40 * 2391141 * 2
def baseEnd_2391141 : Nat := 818536430448356255693899

theorem tailTrace_2391141 : CollatzResearch.WordTrace tailWord_2391141 prefixEnd_2391141 818536430448356255693899 := by
  unfold tailWord_2391141
  simp only [CollatzResearch.WordTrace]
  refine ⟨87212077030312006215565277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58141384686874670810376851 87212077030312006215565277)
  ·
    refine ⟨32704528886367002330836979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87212077030312006215565277 32704528886367002330836979)
    ·
      refine ⟨49056793329550503496255469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32704528886367002330836979 49056793329550503496255469)
      ·
        refine ⟨18396297498581438811095801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49056793329550503496255469 18396297498581438811095801)
        ·
          refine ⟨13797223123936079108321851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18396297498581438811095801 13797223123936079108321851)
          ·
            refine ⟨20695834685904118662482777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13797223123936079108321851 20695834685904118662482777)
            ·
              refine ⟨15521876014428088996862083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20695834685904118662482777 15521876014428088996862083)
              ·
                refine ⟨23282814021642133495293125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15521876014428088996862083 23282814021642133495293125)
                ·
                  refine ⟨4365527629057900030367461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23282814021642133495293125 4365527629057900030367461)
                  ·
                    refine ⟨818536430448356255693899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4365527629057900030367461 818536430448356255693899)
                    ·
                      rfl

theorem cell22_2391141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_2391141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391141 prefixEnd_2391141 := by exact prefixLift 2391141
  have htrace : WordTrace (prefixWord ++ tailWord_2391141) baseStart_2391141 baseEnd_2391141 := by
    simpa [prefixWord, tailWord_2391141, baseEnd_2391141] using wordTrace_append hprefix tailTrace_2391141
  have hstable : (prefixWord ++ tailWord_2391141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391141).length < 2 ^ (prefixWord ++ tailWord_2391141).sum := by decide
  have hdescent : baseEnd_2391141 < baseStart_2391141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391143 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2391143 : Nat := 118140960795 + 2391143 * 2 ^ 59
def prefixEnd_2391143 : Nat := 4983230072969 + 3 ^ 40 * 2391143 * 2
def baseEnd_2391143 : Nat := 818537115089228917143893

theorem tailTrace_2391143 : CollatzResearch.WordTrace tailWord_2391143 prefixEnd_2391143 818537115089228917143893 := by
  unfold tailWord_2391143
  simp only [CollatzResearch.WordTrace]
  refine ⟨87212149976304760557138083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58141433317536507038092055 87212149976304760557138083)
  ·
    refine ⟨130818224964457140835707125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87212149976304760557138083 130818224964457140835707125)
    ·
      refine ⟨12264208590417856953347543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130818224964457140835707125 12264208590417856953347543)
      ·
        refine ⟨18396312885626785430021315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12264208590417856953347543 18396312885626785430021315)
        ·
          refine ⟨27594469328440178145031973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18396312885626785430021315 27594469328440178145031973)
          ·
            refine ⟨5173962999082533402193495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27594469328440178145031973 5173962999082533402193495)
            ·
              refine ⟨7760944498623800103290243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173962999082533402193495 7760944498623800103290243)
              ·
                refine ⟨11641416747935700154935365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760944498623800103290243 11641416747935700154935365)
                ·
                  refine ⟨2182765640237943779050381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11641416747935700154935365 2182765640237943779050381)
                  ·
                    refine ⟨818537115089228917143893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182765640237943779050381 818537115089228917143893)
                    ·
                      rfl

theorem cell22_2391143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2391143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391143 prefixEnd_2391143 := by exact prefixLift 2391143
  have htrace : WordTrace (prefixWord ++ tailWord_2391143) baseStart_2391143 baseEnd_2391143 := by
    simpa [prefixWord, tailWord_2391143, baseEnd_2391143] using wordTrace_append hprefix tailTrace_2391143
  have hstable : (prefixWord ++ tailWord_2391143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391143).length < 2 ^ (prefixWord ++ tailWord_2391143).sum := by decide
  have hdescent : baseEnd_2391143 < baseStart_2391143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391201 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 7]
def baseStart_2391201 : Nat := 118140960795 + 2391201 * 2 ^ 59
def prefixEnd_2391201 : Nat := 4983230072969 + 3 ^ 40 * 2391201 * 2
def baseEnd_2391201 : Nat := 272852323224845366397905

theorem tailTrace_2391201 : CollatzResearch.WordTrace tailWord_2391201 prefixEnd_2391201 272852323224845366397905 := by
  unfold tailWord_2391201
  simp only [CollatzResearch.WordTrace]
  refine ⟨87214265410094636462749457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58142843606729757641832971 87214265410094636462749457)
  ·
    refine ⟨65410699057570977347062093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87214265410094636462749457 65410699057570977347062093)
    ·
      refine ⟨24529012146589116505148285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65410699057570977347062093 24529012146589116505148285)
      ·
        refine ⟨9198379554970918689430607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24529012146589116505148285 9198379554970918689430607)
        ·
          refine ⟨13797569332456378034145911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9198379554970918689430607 13797569332456378034145911)
          ·
            refine ⟨20696353998684567051218867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13797569332456378034145911 20696353998684567051218867)
            ·
              refine ⟨31044530998026850576828301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20696353998684567051218867 31044530998026850576828301)
              ·
                refine ⟨11641699124260068966310613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31044530998026850576828301 11641699124260068966310613)
                ·
                  refine ⟨272852323224845366397905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11641699124260068966310613 272852323224845366397905)
                  ·
                    rfl

theorem cell22_2391201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_2391201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391201 prefixEnd_2391201 := by exact prefixLift 2391201
  have htrace : WordTrace (prefixWord ++ tailWord_2391201) baseStart_2391201 baseEnd_2391201 := by
    simpa [prefixWord, tailWord_2391201, baseEnd_2391201] using wordTrace_append hprefix tailTrace_2391201
  have hstable : (prefixWord ++ tailWord_2391201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391201).length < 2 ^ (prefixWord ++ tailWord_2391201).sum := by decide
  have hdescent : baseEnd_2391201 < baseStart_2391201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391205 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_2391205 : Nat := 118140960795 + 2391205 * 2 ^ 59
def prefixEnd_2391205 : Nat := 4983230072969 + 3 ^ 40 * 2391205 * 2
def baseEnd_2391205 : Nat := 818558338956281422093703

theorem tailTrace_2391205 : CollatzResearch.WordTrace tailWord_2391205 prefixEnd_2391205 818558338956281422093703 := by
  unfold tailWord_2391205
  simp only [CollatzResearch.WordTrace]
  refine ⟨87214411302080145145895069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58142940868053430097263379 87214411302080145145895069)
  ·
    refine ⟨32705404238280054429710651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87214411302080145145895069 32705404238280054429710651)
    ·
      refine ⟨49058106357420081644565977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32705404238280054429710651 49058106357420081644565977)
      ·
        refine ⟨36793579768065061233424483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49058106357420081644565977 36793579768065061233424483)
        ·
          refine ⟨55190369652097591850136725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36793579768065061233424483 55190369652097591850136725)
          ·
            refine ⟨2587048577442074617975159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55190369652097591850136725 2587048577442074617975159)
            ·
              refine ⟨3880572866163111926962739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587048577442074617975159 3880572866163111926962739)
              ·
                refine ⟨5820859299244667890444109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880572866163111926962739 5820859299244667890444109)
                ·
                  refine ⟨2182822237216750458916541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5820859299244667890444109 2182822237216750458916541)
                  ·
                    refine ⟨818558338956281422093703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182822237216750458916541 818558338956281422093703)
                    ·
                      rfl

theorem cell22_2391205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_2391205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391205 prefixEnd_2391205 := by exact prefixLift 2391205
  have htrace : WordTrace (prefixWord ++ tailWord_2391205) baseStart_2391205 baseEnd_2391205 := by
    simpa [prefixWord, tailWord_2391205, baseEnd_2391205] using wordTrace_append hprefix tailTrace_2391205
  have hstable : (prefixWord ++ tailWord_2391205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391205).length < 2 ^ (prefixWord ++ tailWord_2391205).sum := by decide
  have hdescent : baseEnd_2391205 < baseStart_2391205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391218 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_2391218 : Nat := 118140960795 + 2391218 * 2 ^ 59
def prefixEnd_2391218 : Nat := 4983230072969 + 3 ^ 40 * 2391218 * 2
def baseEnd_2391218 : Nat := 272854263040651240506221

theorem tailTrace_2391218 : CollatzResearch.WordTrace tailWord_2391218 prefixEnd_2391218 272854263040651240506221 := by
  unfold tailWord_2391218
  simp only [CollatzResearch.WordTrace]
  refine ⟨21803721362758262091529577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58143256967355365577412205 21803721362758262091529577)
  ·
    refine ⟨16352791022068696568647183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21803721362758262091529577 16352791022068696568647183)
    ·
      refine ⟨24529186533103044852970775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16352791022068696568647183 24529186533103044852970775)
      ·
        refine ⟨36793779799654567279456163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24529186533103044852970775 36793779799654567279456163)
        ·
          refine ⟨55190669699481850919184245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36793779799654567279456163 55190669699481850919184245)
          ·
            refine ⟨5174125284326423523673523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55190669699481850919184245 5174125284326423523673523)
            ·
              refine ⟨7761187926489635285510285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5174125284326423523673523 7761187926489635285510285)
              ·
                refine ⟨2910445472433613232066357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7761187926489635285510285 2910445472433613232066357)
                ·
                  refine ⟨272854263040651240506221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910445472433613232066357 272854263040651240506221)
                  ·
                    rfl

theorem cell22_2391218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_2391218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391218 prefixEnd_2391218 := by exact prefixLift 2391218
  have htrace : WordTrace (prefixWord ++ tailWord_2391218) baseStart_2391218 baseEnd_2391218 := by
    simpa [prefixWord, tailWord_2391218, baseEnd_2391218] using wordTrace_append hprefix tailTrace_2391218
  have hstable : (prefixWord ++ tailWord_2391218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391218).length < 2 ^ (prefixWord ++ tailWord_2391218).sum := by decide
  have hdescent : baseEnd_2391218 < baseStart_2391218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391252 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 5]
def baseStart_2391252 : Nat := 118140960795 + 2391252 * 2 ^ 59
def prefixEnd_2391252 : Nat := 4983230072969 + 3 ^ 40 * 2391252 * 2
def baseEnd_2391252 : Nat := 272858142672262988722853

theorem tailTrace_2391252 : CollatzResearch.WordTrace tailWord_2391252 prefixEnd_2391252 272858142672262988722853 := by
  unfold tailWord_2391252
  simp only [CollatzResearch.WordTrace]
  refine ⟨43608062766454936086428005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58144083688606581448570673 43608062766454936086428005)
  ·
    refine ⟨8176511768710300516205251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43608062766454936086428005 8176511768710300516205251)
    ·
      refine ⟨12264767653065450774307877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8176511768710300516205251 12264767653065450774307877)
      ·
        refine ⟨2299643934949772020182727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12264767653065450774307877 2299643934949772020182727)
        ·
          refine ⟨3449465902424658030274091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299643934949772020182727 3449465902424658030274091)
          ·
            refine ⟨5174198853636987045411137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449465902424658030274091 5174198853636987045411137)
            ·
              refine ⟨3880649140227740284058353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5174198853636987045411137 3880649140227740284058353)
              ·
                refine ⟨2910486855170805213043765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880649140227740284058353 2910486855170805213043765)
                ·
                  refine ⟨272858142672262988722853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910486855170805213043765 272858142672262988722853)
                  ·
                    rfl

theorem cell22_2391252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_2391252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391252 prefixEnd_2391252 := by exact prefixLift 2391252
  have htrace : WordTrace (prefixWord ++ tailWord_2391252) baseStart_2391252 baseEnd_2391252 := by
    simpa [prefixWord, tailWord_2391252, baseEnd_2391252] using wordTrace_append hprefix tailTrace_2391252
  have hstable : (prefixWord ++ tailWord_2391252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391252).length < 2 ^ (prefixWord ++ tailWord_2391252).sum := by decide
  have hdescent : baseEnd_2391252 < baseStart_2391252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391256 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 1, 3]
def baseStart_2391256 : Nat := 118140960795 + 2391256 * 2 ^ 59
def prefixEnd_2391256 : Nat := 4983230072969 + 3 ^ 40 * 2391256 * 2
def baseEnd_2391256 : Nat := 818575797298534289068547

theorem tailTrace_2391256 : CollatzResearch.WordTrace tailWord_2391256 prefixEnd_2391256 818575797298534289068547 := by
  unfold tailWord_2391256
  simp only [CollatzResearch.WordTrace]
  refine ⟨43608135712447690428000811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58144180949930253904001081 43608135712447690428000811)
  ·
    refine ⟨65412203568671535642001217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43608135712447690428000811 65412203568671535642001217)
    ·
      refine ⟨49059152676503651731500913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65412203568671535642001217 49059152676503651731500913)
      ·
        refine ⟨36794364507377738798625685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49059152676503651731500913 36794364507377738798625685)
        ·
          refine ⟨1724735836283331506185579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36794364507377738798625685 1724735836283331506185579)
          ·
            refine ⟨2587103754424997259278369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724735836283331506185579 2587103754424997259278369)
            ·
              refine ⟨1940327815818747944458777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2587103754424997259278369 1940327815818747944458777)
              ·
                refine ⟨1455245861864060958344083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940327815818747944458777 1455245861864060958344083)
                ·
                  refine ⟨2182868792796091437516125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455245861864060958344083 2182868792796091437516125)
                  ·
                    refine ⟨818575797298534289068547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182868792796091437516125 818575797298534289068547)
                    ·
                      rfl

theorem cell22_2391256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_2391256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391256 prefixEnd_2391256 := by exact prefixLift 2391256
  have htrace : WordTrace (prefixWord ++ tailWord_2391256) baseStart_2391256 baseEnd_2391256 := by
    simpa [prefixWord, tailWord_2391256, baseEnd_2391256] using wordTrace_append hprefix tailTrace_2391256
  have hstable : (prefixWord ++ tailWord_2391256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391256).length < 2 ^ (prefixWord ++ tailWord_2391256).sum := by decide
  have hdescent : baseEnd_2391256 < baseStart_2391256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391278 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2391278 : Nat := 118140960795 + 2391278 * 2 ^ 59
def prefixEnd_2391278 : Nat := 4983230072969 + 3 ^ 40 * 2391278 * 2
def baseEnd_2391278 : Nat := 818583328348133565018479

theorem tailTrace_2391278 : CollatzResearch.WordTrace tailWord_2391278 prefixEnd_2391278 818583328348133565018479 := by
  unfold tailWord_2391278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902134228851959826662811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58144715887210452408868325 10902134228851959826662811)
  ·
    refine ⟨16353201343277939739994217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10902134228851959826662811 16353201343277939739994217)
    ·
      refine ⟨12264901007458454804995663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16353201343277939739994217 12264901007458454804995663)
      ·
        refine ⟨18397351511187682207493495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12264901007458454804995663 18397351511187682207493495)
        ·
          refine ⟨27596027266781523311240243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18397351511187682207493495 27596027266781523311240243)
          ·
            refine ⟨41394040900172284966860365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27596027266781523311240243 41394040900172284966860365)
            ·
              refine ⟨15522765337564606862572637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41394040900172284966860365 15522765337564606862572637)
              ·
                refine ⟨5821037001586727573464739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15522765337564606862572637 5821037001586727573464739)
                ·
                  refine ⟨8731555502380091360197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5821037001586727573464739 8731555502380091360197109)
                  ·
                    refine ⟨818583328348133565018479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8731555502380091360197109 818583328348133565018479)
                    ·
                      rfl

theorem cell22_2391278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2391278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391278 prefixEnd_2391278 := by exact prefixLift 2391278
  have htrace : WordTrace (prefixWord ++ tailWord_2391278) baseStart_2391278 baseEnd_2391278 := by
    simpa [prefixWord, tailWord_2391278, baseEnd_2391278] using wordTrace_append hprefix tailTrace_2391278
  have hstable : (prefixWord ++ tailWord_2391278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391278).length < 2 ^ (prefixWord ++ tailWord_2391278).sum := by decide
  have hdescent : baseEnd_2391278 < baseStart_2391278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391374 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_2391374 : Nat := 118140960795 + 2391374 * 2 ^ 59
def prefixEnd_2391374 : Nat := 4983230072969 + 3 ^ 40 * 2391374 * 2
def baseEnd_2391374 : Nat := 818616191110021314618185

theorem tailTrace_2391374 : CollatzResearch.WordTrace tailWord_2391374 prefixEnd_2391374 818616191110021314618185 := by
  unfold tailWord_2391374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902571904808485876099647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58147050158978591339198117 10902571904808485876099647)
  ·
    refine ⟨16353857857212728814149471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10902571904808485876099647 16353857857212728814149471)
    ·
      refine ⟨24530786785819093221224207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16353857857212728814149471 24530786785819093221224207)
      ·
        refine ⟨36796180178728639831836311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24530786785819093221224207 36796180178728639831836311)
        ·
          refine ⟨55194270268092959747754467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36796180178728639831836311 55194270268092959747754467)
          ·
            refine ⟨82791405402139439621631701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55194270268092959747754467 82791405402139439621631701)
            ·
              refine ⟨1940423564112643116131993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82791405402139439621631701 1940423564112643116131993)
              ·
                refine ⟨1455317673084482337098995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940423564112643116131993 1455317673084482337098995)
                ·
                  refine ⟨2182976509626723505648493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455317673084482337098995 2182976509626723505648493)
                  ·
                    refine ⟨818616191110021314618185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182976509626723505648493 818616191110021314618185)
                    ·
                      rfl

theorem cell22_2391374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_2391374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391374 prefixEnd_2391374 := by exact prefixLift 2391374
  have htrace : WordTrace (prefixWord ++ tailWord_2391374) baseStart_2391374 baseEnd_2391374 := by
    simpa [prefixWord, tailWord_2391374, baseEnd_2391374] using wordTrace_append hprefix tailTrace_2391374
  have hstable : (prefixWord ++ tailWord_2391374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391374).length < 2 ^ (prefixWord ++ tailWord_2391374).sum := by decide
  have hdescent : baseEnd_2391374 < baseStart_2391374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391415 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 4]
def baseStart_2391415 : Nat := 118140960795 + 2391415 * 2 ^ 59
def prefixEnd_2391415 : Nat := 4983230072969 + 3 ^ 40 * 2391415 * 2
def baseEnd_2391415 : Nat := 272876742082636958114353

theorem tailTrace_2391415 : CollatzResearch.WordTrace tailWord_2391415 prefixEnd_2391415 272876742082636958114353 := by
  unfold tailWord_2391415
  simp only [CollatzResearch.WordTrace]
  refine ⟨87222070631319351011039699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58148047087546234007359799 87222070631319351011039699)
  ·
    refine ⟨130833105946979026516559549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87222070631319351011039699 130833105946979026516559549)
    ·
      refine ⟨49062414730117134943709831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130833105946979026516559549 49062414730117134943709831)
      ·
        refine ⟨73593622095175702415564747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49062414730117134943709831 73593622095175702415564747)
        ·
          refine ⟨110390433142763553623347121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73593622095175702415564747 110390433142763553623347121)
          ·
            refine ⟨82792824857072665217510341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110390433142763553623347121 82792824857072665217510341)
            ·
              refine ⟨15523654660701124728283189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82792824857072665217510341 15523654660701124728283189)
              ·
                refine ⟨1455342624440730443276549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15523654660701124728283189 1455342624440730443276549)
                ·
                  refine ⟨272876742082636958114353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455342624440730443276549 272876742082636958114353)
                  ·
                    rfl

theorem cell22_2391415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 4].length) (baseStart_2391415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391415 prefixEnd_2391415 := by exact prefixLift 2391415
  have htrace : WordTrace (prefixWord ++ tailWord_2391415) baseStart_2391415 baseEnd_2391415 := by
    simpa [prefixWord, tailWord_2391415, baseEnd_2391415] using wordTrace_append hprefix tailTrace_2391415
  have hstable : (prefixWord ++ tailWord_2391415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391415).length < 2 ^ (prefixWord ++ tailWord_2391415).sum := by decide
  have hdescent : baseEnd_2391415 < baseStart_2391415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391432 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 4]
def baseStart_2391432 : Nat := 118140960795 + 2391432 * 2 ^ 59
def prefixEnd_2391432 : Nat := 4983230072969 + 3 ^ 40 * 2391432 * 2
def baseEnd_2391432 : Nat := 272878681898442832222669

theorem tailTrace_2391432 : CollatzResearch.WordTrace tailWord_2391432 prefixEnd_2391432 272878681898442832222669 := by
  unfold tailWord_2391432
  simp only [CollatzResearch.WordTrace]
  refine ⟨43611345336128881457204275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58148460448171841942939033 43611345336128881457204275)
  ·
    refine ⟨65417018004193322185806413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43611345336128881457204275 65417018004193322185806413)
    ·
      refine ⟨24531381751572495819677405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65417018004193322185806413 24531381751572495819677405)
      ·
        refine ⟨9199268156839685932379027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24531381751572495819677405 9199268156839685932379027)
        ·
          refine ⟨13798902235259528898568541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9199268156839685932379027 13798902235259528898568541)
          ·
            refine ⟨5174588338222323336963203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13798902235259528898568541 5174588338222323336963203)
            ·
              refine ⟨7761882507333485005444805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5174588338222323336963203 7761882507333485005444805)
              ·
                refine ⟨1455352970125028438520901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7761882507333485005444805 1455352970125028438520901)
                ·
                  refine ⟨272878681898442832222669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455352970125028438520901 272878681898442832222669)
                  ·
                    rfl

theorem cell22_2391432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_2391432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391432 prefixEnd_2391432 := by exact prefixLift 2391432
  have htrace : WordTrace (prefixWord ++ tailWord_2391432) baseStart_2391432 baseEnd_2391432 := by
    simpa [prefixWord, tailWord_2391432, baseEnd_2391432] using wordTrace_append hprefix tailTrace_2391432
  have hstable : (prefixWord ++ tailWord_2391432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391432).length < 2 ^ (prefixWord ++ tailWord_2391432).sum := by decide
  have hdescent : baseEnd_2391432 < baseStart_2391432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391481 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 2, 3]
def baseStart_2391481 : Nat := 118140960795 + 2391481 * 2 ^ 59
def prefixEnd_2391481 : Nat := 4983230072969 + 3 ^ 40 * 2391481 * 2
def baseEnd_2391481 : Nat := 818652819396708702192857

theorem tailTrace_2391481 : CollatzResearch.WordTrace tailWord_2391481 prefixEnd_2391481 818652819396708702192857 := by
  unfold tailWord_2391481
  simp only [CollatzResearch.WordTrace]
  refine ⟨87224477849080244282942297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58149651899386829521961531 87224477849080244282942297)
  ·
    refine ⟨65418358386810183212206723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87224477849080244282942297 65418358386810183212206723)
    ·
      refine ⟨98127537580215274818310085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65418358386810183212206723 98127537580215274818310085)
      ·
        refine ⟨18398913296290364028433141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98127537580215274818310085 18398913296290364028433141)
        ·
          refine ⟨1724898121527221627665607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18398913296290364028433141 1724898121527221627665607)
          ·
            refine ⟨2587347182290832441498411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724898121527221627665607 2587347182290832441498411)
            ·
              refine ⟨3881020773436248662247617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587347182290832441498411 3881020773436248662247617)
              ·
                refine ⟨2910765580077186496685713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3881020773436248662247617 2910765580077186496685713)
                ·
                  refine ⟨2183074185057889872514285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910765580077186496685713 2183074185057889872514285)
                  ·
                    refine ⟨818652819396708702192857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2183074185057889872514285 818652819396708702192857)
                    ·
                      rfl

theorem cell22_2391481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_2391481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391481 prefixEnd_2391481 := by exact prefixLift 2391481
  have htrace : WordTrace (prefixWord ++ tailWord_2391481) baseStart_2391481 baseEnd_2391481 := by
    simpa [prefixWord, tailWord_2391481, baseEnd_2391481] using wordTrace_append hprefix tailTrace_2391481
  have hstable : (prefixWord ++ tailWord_2391481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391481).length < 2 ^ (prefixWord ++ tailWord_2391481).sum := by decide
  have hdescent : baseEnd_2391481 < baseStart_2391481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391556 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 5]
def baseStart_2391556 : Nat := 118140960795 + 2391556 * 2 ^ 59
def prefixEnd_2391556 : Nat := 4983230072969 + 3 ^ 40 * 2391556 * 2
def baseEnd_2391556 : Nat := 272892831143144502189209

theorem tailTrace_2391556 : CollatzResearch.WordTrace tailWord_2391556 prefixEnd_2391556 272892831143144502189209 := by
  unfold tailWord_2391556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43613606661904266045961261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58151475549205688061281681 43613606661904266045961261)
  ·
    refine ⟨16355102498214099767235473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43613606661904266045961261 16355102498214099767235473)
    ·
      refine ⟨12266326873660574825426605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16355102498214099767235473 12266326873660574825426605)
      ·
        refine ⟨4599872577622715559534977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12266326873660574825426605 4599872577622715559534977)
        ·
          refine ⟨3449904433217036669651233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4599872577622715559534977 3449904433217036669651233)
          ·
            refine ⟨2587428324912777502238425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3449904433217036669651233 2587428324912777502238425)
            ·
              refine ⟨1940571243684583126678819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2587428324912777502238425 1940571243684583126678819)
              ·
                refine ⟨2910856865526874690018229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940571243684583126678819 2910856865526874690018229)
                ·
                  refine ⟨272892831143144502189209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910856865526874690018229 272892831143144502189209)
                  ·
                    rfl

theorem cell22_2391556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_2391556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391556 prefixEnd_2391556 := by exact prefixLift 2391556
  have htrace : WordTrace (prefixWord ++ tailWord_2391556) baseStart_2391556 baseEnd_2391556 := by
    simpa [prefixWord, tailWord_2391556, baseEnd_2391556] using wordTrace_append hprefix tailTrace_2391556
  have hstable : (prefixWord ++ tailWord_2391556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391556).length < 2 ^ (prefixWord ++ tailWord_2391556).sum := by decide
  have hdescent : baseEnd_2391556 < baseStart_2391556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391640 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_2391640 : Nat := 118140960795 + 2391640 * 2 ^ 59
def prefixEnd_2391640 : Nat := 4983230072969 + 3 ^ 40 * 2391640 * 2
def baseEnd_2391640 : Nat := 272902416115361762489123

theorem tailTrace_2391640 : CollatzResearch.WordTrace tailWord_2391640 prefixEnd_2391640 272902416115361762489123 := by
  unfold tailWord_2391640
  simp only [CollatzResearch.WordTrace]
  refine ⟨43615138527752107218990187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58153518037002809625320249 43615138527752107218990187)
  ·
    refine ⟨65422707791628160828485281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43615138527752107218990187 65422707791628160828485281)
    ·
      refine ⟨49067030843721120621363961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65422707791628160828485281 49067030843721120621363961)
      ·
        refine ⟨36800273132790840466022971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49067030843721120621363961 36800273132790840466022971)
        ·
          refine ⟨55200409699186260699034457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36800273132790840466022971 55200409699186260699034457)
          ·
            refine ⟨41400307274389695524275843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55200409699186260699034457 41400307274389695524275843)
            ·
              refine ⟨62100460911584543286413765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41400307274389695524275843 62100460911584543286413765)
              ·
                refine ⟨11643836420922101866202581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62100460911584543286413765 11643836420922101866202581)
                ·
                  refine ⟨272902416115361762489123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11643836420922101866202581 272902416115361762489123)
                  ·
                    rfl

theorem cell22_2391640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_2391640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391640 prefixEnd_2391640 := by exact prefixLift 2391640
  have htrace : WordTrace (prefixWord ++ tailWord_2391640) baseStart_2391640 baseEnd_2391640 := by
    simpa [prefixWord, tailWord_2391640, baseEnd_2391640] using wordTrace_append hprefix tailTrace_2391640
  have hstable : (prefixWord ++ tailWord_2391640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391640).length < 2 ^ (prefixWord ++ tailWord_2391640).sum := by decide
  have hdescent : baseEnd_2391640 < baseStart_2391640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391657 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 5]
def baseStart_2391657 : Nat := 118140960795 + 2391657 * 2 ^ 59
def prefixEnd_2391657 : Nat := 4983230072969 + 3 ^ 40 * 2391657 * 2
def baseEnd_2391657 : Nat := 272904355931167636597439

theorem tailTrace_2391657 : CollatzResearch.WordTrace tailWord_2391657 prefixEnd_2391657 272904355931167636597439 := by
  unfold tailWord_2391657
  simp only [CollatzResearch.WordTrace]
  refine ⟨87230897096442626341349225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58153931397628417560899483 87230897096442626341349225)
  ·
    refine ⟨65423172822331969756011919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87230897096442626341349225 65423172822331969756011919)
    ·
      refine ⟨98134759233497954634017879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65423172822331969756011919 98134759233497954634017879)
      ·
        refine ⟨147202138850246931951026819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98134759233497954634017879 147202138850246931951026819)
        ·
          refine ⟨220803208275370397926540229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147202138850246931951026819 220803208275370397926540229)
          ·
            refine ⟨41400601551631949611226293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220803208275370397926540229 41400601551631949611226293)
            ·
              refine ⟨3881306395465495276052465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41400601551631949611226293 3881306395465495276052465)
              ·
                refine ⟨2910979796599121457039349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3881306395465495276052465 2910979796599121457039349)
                ·
                  refine ⟨272904355931167636597439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910979796599121457039349 272904355931167636597439)
                  ·
                    rfl

theorem cell22_2391657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_2391657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391657 prefixEnd_2391657 := by exact prefixLift 2391657
  have htrace : WordTrace (prefixWord ++ tailWord_2391657) baseStart_2391657 baseEnd_2391657 := by
    simpa [prefixWord, tailWord_2391657, baseEnd_2391657] using wordTrace_append hprefix tailTrace_2391657
  have hstable : (prefixWord ++ tailWord_2391657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391657).length < 2 ^ (prefixWord ++ tailWord_2391657).sum := by decide
  have hdescent : baseEnd_2391657 < baseStart_2391657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391661 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2391661 : Nat := 118140960795 + 2391661 * 2 ^ 59
def prefixEnd_2391661 : Nat := 4983230072969 + 3 ^ 40 * 2391661 * 2
def baseEnd_2391661 : Nat := 818714437075248232692305

theorem tailTrace_2391661 : CollatzResearch.WordTrace tailWord_2391661 prefixEnd_2391661 818714437075248232692305 := by
  unfold tailWord_2391661
  simp only [CollatzResearch.WordTrace]
  refine ⟨87231042988428135024494837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58154028658952090016329891 87231042988428135024494837)
  ·
    refine ⟨8177910280165137658546391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87231042988428135024494837 8177910280165137658546391)
    ·
      refine ⟨12266865420247706487819587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8177910280165137658546391 12266865420247706487819587)
      ·
        refine ⟨18400298130371559731729381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12266865420247706487819587 18400298130371559731729381)
        ·
          refine ⟨3450055899444667449699259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18400298130371559731729381 3450055899444667449699259)
          ·
            refine ⟨5175083849167001174548889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3450055899444667449699259 5175083849167001174548889)
            ·
              refine ⟨3881312886875250880911667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5175083849167001174548889 3881312886875250880911667)
              ·
                refine ⟨5821969330312876321367501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881312886875250880911667 5821969330312876321367501)
                ·
                  refine ⟨2183238498867328620512813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5821969330312876321367501 2183238498867328620512813)
                  ·
                    refine ⟨818714437075248232692305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2183238498867328620512813 818714437075248232692305)
                    ·
                      rfl

theorem cell22_2391661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2391661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391661 prefixEnd_2391661 := by exact prefixLift 2391661
  have htrace : WordTrace (prefixWord ++ tailWord_2391661) baseStart_2391661 baseEnd_2391661 := by
    simpa [prefixWord, tailWord_2391661, baseEnd_2391661] using wordTrace_append hprefix tailTrace_2391661
  have hstable : (prefixWord ++ tailWord_2391661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391661).length < 2 ^ (prefixWord ++ tailWord_2391661).sum := by decide
  have hdescent : baseEnd_2391661 < baseStart_2391661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391704 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_2391704 : Nat := 118140960795 + 2391704 * 2 ^ 59
def prefixEnd_2391704 : Nat := 4983230072969 + 3 ^ 40 * 2391704 * 2
def baseEnd_2391704 : Nat := 818729156854010453867173

theorem tailTrace_2391704 : CollatzResearch.WordTrace tailWord_2391704 prefixEnd_2391704 818729156854010453867173 := by
  unfold tailWord_2391704
  simp only [CollatzResearch.WordTrace]
  refine ⟨43616305663636176684155083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58155074218181568912206777 43616305663636176684155083)
  ·
    refine ⟨65424458495454265026232625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43616305663636176684155083 65424458495454265026232625)
    ·
      refine ⟨49068343871590698769674469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65424458495454265026232625 49068343871590698769674469)
      ·
        refine ⟨9200314475923256019313963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49068343871590698769674469 9200314475923256019313963)
        ·
          refine ⟨13800471713884884028970945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9200314475923256019313963 13800471713884884028970945)
          ·
            refine ⟨10350353785413663021728209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13800471713884884028970945 10350353785413663021728209)
            ·
              refine ⟨7762765339060247266296157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10350353785413663021728209 7762765339060247266296157)
              ·
                refine ⟨2911037002147592724861059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7762765339060247266296157 2911037002147592724861059)
                ·
                  refine ⟨4366555503221389087291589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911037002147592724861059 4366555503221389087291589)
                  ·
                    refine ⟨818729156854010453867173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4366555503221389087291589 818729156854010453867173)
                    ·
                      rfl

theorem cell22_2391704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_2391704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391704 prefixEnd_2391704 := by exact prefixLift 2391704
  have htrace : WordTrace (prefixWord ++ tailWord_2391704) baseStart_2391704 baseEnd_2391704 := by
    simpa [prefixWord, tailWord_2391704, baseEnd_2391704] using wordTrace_append hprefix tailTrace_2391704
  have hstable : (prefixWord ++ tailWord_2391704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391704).length < 2 ^ (prefixWord ++ tailWord_2391704).sum := by decide
  have hdescent : baseEnd_2391704 < baseStart_2391704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391826 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_2391826 : Nat := 118140960795 + 2391826 * 2 ^ 59
def prefixEnd_2391826 : Nat := 4983230072969 + 3 ^ 40 * 2391826 * 2
def baseEnd_2391826 : Nat := 272923639982414267438933

theorem tailTrace_2391826 : CollatzResearch.WordTrace tailWord_2391826 prefixEnd_2391826 272923639982414267438933 := by
  unfold tailWord_2391826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21809265258207592051062833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58158040688553578802834221 21809265258207592051062833)
  ·
    refine ⟨16356948943655694038297125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21809265258207592051062833 16356948943655694038297125)
    ·
      refine ⟨3066927926935442632180711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16356948943655694038297125 3066927926935442632180711)
      ·
        refine ⟨4600391890403163948271067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066927926935442632180711 4600391890403163948271067)
        ·
          refine ⟨6900587835604745922406601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4600391890403163948271067 6900587835604745922406601)
          ·
            refine ⟨5175440876703559441804951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6900587835604745922406601 5175440876703559441804951)
            ·
              refine ⟨7763161315055339162707427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5175440876703559441804951 7763161315055339162707427)
              ·
                refine ⟨11644741972583008744061141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763161315055339162707427 11644741972583008744061141)
                ·
                  refine ⟨272923639982414267438933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11644741972583008744061141 272923639982414267438933)
                  ·
                    rfl

theorem cell22_2391826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_2391826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391826 prefixEnd_2391826 := by exact prefixLift 2391826
  have htrace : WordTrace (prefixWord ++ tailWord_2391826) baseStart_2391826 baseEnd_2391826 := by
    simpa [prefixWord, tailWord_2391826, baseEnd_2391826] using wordTrace_append hprefix tailTrace_2391826
  have hstable : (prefixWord ++ tailWord_2391826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391826).length < 2 ^ (prefixWord ++ tailWord_2391826).sum := by decide
  have hdescent : baseEnd_2391826 < baseStart_2391826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391903 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 2, 3]
def baseStart_2391903 : Nat := 118140960795 + 2391903 * 2 ^ 59
def prefixEnd_2391903 : Nat := 4983230072969 + 3 ^ 40 * 2391903 * 2
def baseEnd_2391903 : Nat := 818797278620840268141563

theorem tailTrace_2391903 : CollatzResearch.WordTrace tailWord_2391903 prefixEnd_2391903 818797278620840268141563 := by
  unfold tailWord_2391903
  simp only [CollatzResearch.WordTrace]
  refine ⟨87239869453551410354804363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58159912969034273569869575 87239869453551410354804363)
  ·
    refine ⟨130859804180327115532206545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87239869453551410354804363 130859804180327115532206545)
    ·
      refine ⟨98144853135245336649154909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130859804180327115532206545 98144853135245336649154909)
      ·
        refine ⟨36804319925717001243433091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98144853135245336649154909 36804319925717001243433091)
        ·
          refine ⟨55206479888575501865149637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36804319925717001243433091 55206479888575501865149637)
          ·
            refine ⟨10351214979107906599715557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55206479888575501865149637 10351214979107906599715557)
            ·
              refine ⟨1940852808582732487446667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10351214979107906599715557 1940852808582732487446667)
              ·
                refine ⟨2911279212874098731170001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940852808582732487446667 2911279212874098731170001)
                ·
                  refine ⟨2183459409655574048377501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911279212874098731170001 2183459409655574048377501)
                  ·
                    refine ⟨818797278620840268141563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2183459409655574048377501 818797278620840268141563)
                    ·
                      rfl

theorem cell22_2391903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_2391903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391903 prefixEnd_2391903 := by exact prefixLift 2391903
  have htrace : WordTrace (prefixWord ++ tailWord_2391903) baseStart_2391903 baseEnd_2391903 := by
    simpa [prefixWord, tailWord_2391903, baseEnd_2391903] using wordTrace_append hprefix tailTrace_2391903
  have hstable : (prefixWord ++ tailWord_2391903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391903).length < 2 ^ (prefixWord ++ tailWord_2391903).sum := by decide
  have hdescent : baseEnd_2391903 < baseStart_2391903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391918 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2391918 : Nat := 118140960795 + 2391918 * 2 ^ 59
def prefixEnd_2391918 : Nat := 4983230072969 + 3 ^ 40 * 2391918 * 2
def baseEnd_2391918 : Nat := 818802413427385229016517

theorem tailTrace_2391918 : CollatzResearch.WordTrace tailWord_2391918 prefixEnd_2391918 818802413427385229016517 := by
  unfold tailWord_2391918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905052068562133489575051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58160277698998045277733605 10905052068562133489575051)
  ·
    refine ⟨16357578102843200234362577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10905052068562133489575051 16357578102843200234362577)
    ·
      refine ⟨12268183577132400175771933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16357578102843200234362577 12268183577132400175771933)
      ·
        refine ⟨4600568841424650065914475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12268183577132400175771933 4600568841424650065914475)
        ·
          refine ⟨6900853262136975098871713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4600568841424650065914475 6900853262136975098871713)
          ·
            refine ⟨5175639946602731324153785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6900853262136975098871713 5175639946602731324153785)
            ·
              refine ⟨3881729959952048493115339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5175639946602731324153785 3881729959952048493115339)
              ·
                refine ⟨5822594939928072739673009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881729959952048493115339 5822594939928072739673009)
                ·
                  refine ⟨4366946204946054554754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5822594939928072739673009 4366946204946054554754757)
                  ·
                    refine ⟨818802413427385229016517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4366946204946054554754757 818802413427385229016517)
                    ·
                      rfl

theorem cell22_2391918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2391918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391918 prefixEnd_2391918 := by exact prefixLift 2391918
  have htrace : WordTrace (prefixWord ++ tailWord_2391918) baseStart_2391918 baseEnd_2391918 := by
    simpa [prefixWord, tailWord_2391918, baseEnd_2391918] using wordTrace_append hprefix tailTrace_2391918
  have hstable : (prefixWord ++ tailWord_2391918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391918).length < 2 ^ (prefixWord ++ tailWord_2391918).sum := by decide
  have hdescent : baseEnd_2391918 < baseStart_2391918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391950 : List Nat := [4, 1, 1, 5, 2, 1, 1, 7]
def baseStart_2391950 : Nat := 118140960795 + 2391950 * 2 ^ 59
def prefixEnd_2391950 : Nat := 4983230072969 + 3 ^ 40 * 2391950 * 2
def baseEnd_2391950 : Nat := 90979263075705312468491

theorem tailTrace_2391950 : CollatzResearch.WordTrace tailWord_2391950 prefixEnd_2391950 90979263075705312468491 := by
  unfold tailWord_2391950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905197960547642172720663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58161055789587424921176869 10905197960547642172720663)
  ·
    refine ⟨16357796940821463259080995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10905197960547642172720663 16357796940821463259080995)
    ·
      refine ⟨24536695411232194888621493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16357796940821463259080995 24536695411232194888621493)
      ·
        refine ⟨2300315194803018270808265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24536695411232194888621493 2300315194803018270808265)
        ·
          refine ⟨1725236396102263703106199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2300315194803018270808265 1725236396102263703106199)
          ·
            refine ⟨2587854594153395554659299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725236396102263703106199 2587854594153395554659299)
            ·
              refine ⟨3881781891230093331988949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587854594153395554659299 3881781891230093331988949)
              ·
                refine ⟨90979263075705312468491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3881781891230093331988949 90979263075705312468491)
                ·
                  rfl

theorem cell22_2391950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_2391950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391950 prefixEnd_2391950 := by exact prefixLift 2391950
  have htrace : WordTrace (prefixWord ++ tailWord_2391950) baseStart_2391950 baseEnd_2391950 := by
    simpa [prefixWord, tailWord_2391950, baseEnd_2391950] using wordTrace_append hprefix tailTrace_2391950
  have hstable : (prefixWord ++ tailWord_2391950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391950).length < 2 ^ (prefixWord ++ tailWord_2391950).sum := by decide
  have hdescent : baseEnd_2391950 < baseStart_2391950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391959 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2391959 : Nat := 118140960795 + 2391959 * 2 ^ 59
def prefixEnd_2391959 : Nat := 4983230072969 + 3 ^ 40 * 2391959 * 2
def baseEnd_2391959 : Nat := 818816448565274788741391

theorem tailTrace_2391959 : CollatzResearch.WordTrace tailWord_2391959 prefixEnd_2391959 818816448565274788741391 := by
  unfold tailWord_2391959
  simp only [CollatzResearch.WordTrace]
  refine ⟨87241911941348531918842931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58161274627565687945895287 87241911941348531918842931)
  ·
    refine ⟨130862867912022797878264397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87241911941348531918842931 130862867912022797878264397)
    ·
      refine ⟨49073575467008549204349149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130862867912022797878264397 49073575467008549204349149)
      ·
        refine ⟨18402590800128205951630931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49073575467008549204349149 18402590800128205951630931)
        ·
          refine ⟨27603886200192308927446397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18402590800128205951630931 27603886200192308927446397)
          ·
            refine ⟨10351457325072115847792399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27603886200192308927446397 10351457325072115847792399)
            ·
              refine ⟨15527185987608173771688599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10351457325072115847792399 15527185987608173771688599)
              ·
                refine ⟨23290778981412260657532899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15527185987608173771688599 23290778981412260657532899)
                ·
                  refine ⟨34936168472118390986299349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23290778981412260657532899 34936168472118390986299349)
                  ·
                    refine ⟨818816448565274788741391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34936168472118390986299349 818816448565274788741391)
                    ·
                      rfl

theorem cell22_2391959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2391959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2391959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2391959 prefixEnd_2391959 := by exact prefixLift 2391959
  have htrace : WordTrace (prefixWord ++ tailWord_2391959) baseStart_2391959 baseEnd_2391959 := by
    simpa [prefixWord, tailWord_2391959, baseEnd_2391959] using wordTrace_append hprefix tailTrace_2391959
  have hstable : (prefixWord ++ tailWord_2391959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391959).length < 2 ^ (prefixWord ++ tailWord_2391959).sum := by decide
  have hdescent : baseEnd_2391959 < baseStart_2391959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392036 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_2392036 : Nat := 118140960795 + 2392036 * 2 ^ 59
def prefixEnd_2392036 : Nat := 4983230072969 + 3 ^ 40 * 2392036 * 2
def baseEnd_2392036 : Nat := 818842807238872254566155

theorem tailTrace_2392036 : CollatzResearch.WordTrace tailWord_2392036 prefixEnd_2392036 818842807238872254566155 := by
  unfold tailWord_2392036
  simp only [CollatzResearch.WordTrace]
  refine ⟨43622360181034787034697981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58163146908046382712930641 43622360181034787034697981)
  ·
    refine ⟨16358385067888045138011743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43622360181034787034697981 16358385067888045138011743)
    ·
      refine ⟨24537577601832067707017615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16358385067888045138011743 24537577601832067707017615)
      ·
        refine ⟨36806366402748101560526423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24537577601832067707017615 36806366402748101560526423)
        ·
          refine ⟨55209549604122152340789635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36806366402748101560526423 55209549604122152340789635)
          ·
            refine ⟨82814324406183228511184453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55209549604122152340789635 82814324406183228511184453)
            ·
              refine ⟨15527685826159355345847085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82814324406183228511184453 15527685826159355345847085)
              ·
                refine ⟨5822882184809758254692657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15527685826159355345847085 5822882184809758254692657)
                ·
                  refine ⟨4367161638607318691019493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5822882184809758254692657 4367161638607318691019493)
                  ·
                    refine ⟨818842807238872254566155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367161638607318691019493 818842807238872254566155)
                    ·
                      rfl

theorem cell22_2392036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_2392036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392036 prefixEnd_2392036 := by exact prefixLift 2392036
  have htrace : WordTrace (prefixWord ++ tailWord_2392036) baseStart_2392036 baseEnd_2392036 := by
    simpa [prefixWord, tailWord_2392036, baseEnd_2392036] using wordTrace_append hprefix tailTrace_2392036
  have hstable : (prefixWord ++ tailWord_2392036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392036).length < 2 ^ (prefixWord ++ tailWord_2392036).sum := by decide
  have hdescent : baseEnd_2392036 < baseStart_2392036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392113 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 5]
def baseStart_2392113 : Nat := 118140960795 + 2392113 * 2 ^ 59
def prefixEnd_2392113 : Nat := 4983230072969 + 3 ^ 40 * 2392113 * 2
def baseEnd_2392113 : Nat := 272956388637489906796973

theorem tailTrace_2392113 : CollatzResearch.WordTrace tailWord_2392113 prefixEnd_2392113 272956388637489906796973 := by
  unfold tailWord_2392113
  simp only [CollatzResearch.WordTrace]
  refine ⟨87247528782790616219948993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58165019188527077479965995 87247528782790616219948993)
  ·
    refine ⟨65435646587092962164961745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87247528782790616219948993 65435646587092962164961745)
    ·
      refine ⟨49076734940319721623721309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65435646587092962164961745 49076734940319721623721309)
      ·
        refine ⟨18403775602619895608895491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49076734940319721623721309 18403775602619895608895491)
        ·
          refine ⟨27605663403929843413343237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18403775602619895608895491 27605663403929843413343237)
          ·
            refine ⟨5176061888236845640001857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27605663403929843413343237 5176061888236845640001857)
            ·
              refine ⟨3882046416177634230001393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5176061888236845640001857 3882046416177634230001393)
              ·
                refine ⟨2911534812133225672501045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3882046416177634230001393 2911534812133225672501045)
                ·
                  refine ⟨272956388637489906796973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2911534812133225672501045 272956388637489906796973)
                  ·
                    rfl

theorem cell22_2392113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_2392113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392113 prefixEnd_2392113 := by exact prefixLift 2392113
  have htrace : WordTrace (prefixWord ++ tailWord_2392113) baseStart_2392113 baseEnd_2392113 := by
    simpa [prefixWord, tailWord_2392113, baseEnd_2392113] using wordTrace_append hprefix tailTrace_2392113
  have hstable : (prefixWord ++ tailWord_2392113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392113).length < 2 ^ (prefixWord ++ tailWord_2392113).sum := by decide
  have hdescent : baseEnd_2392113 < baseStart_2392113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392117 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2392117 : Nat := 118140960795 + 2392117 * 2 ^ 59
def prefixEnd_2392117 : Nat := 4983230072969 + 3 ^ 40 * 2392117 * 2
def baseEnd_2392117 : Nat := 818870535194215043290907

theorem tailTrace_2392117 : CollatzResearch.WordTrace tailWord_2392117 prefixEnd_2392117 818870535194215043290907 := by
  unfold tailWord_2392117
  simp only [CollatzResearch.WordTrace]
  refine ⟨87247674674776124903094605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58165116449850749935396403 87247674674776124903094605)
  ·
    refine ⟨32717878003041046838660477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87247674674776124903094605 32717878003041046838660477)
    ·
      refine ⟨12269204251140392564497679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32717878003041046838660477 12269204251140392564497679)
      ·
        refine ⟨18403806376710588846746519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12269204251140392564497679 18403806376710588846746519)
        ·
          refine ⟨27605709565065883270119779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18403806376710588846746519 27605709565065883270119779)
          ·
            refine ⟨41408564347598824905179669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27605709565065883270119779 41408564347598824905179669)
            ·
              refine ⟨1941026453793694917430297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41408564347598824905179669 1941026453793694917430297)
              ·
                refine ⟨1455769840345271188072723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1941026453793694917430297 1455769840345271188072723)
                ·
                  refine ⟨2183654760517906782109085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455769840345271188072723 2183654760517906782109085)
                  ·
                    refine ⟨818870535194215043290907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2183654760517906782109085 818870535194215043290907)
                    ·
                      rfl

theorem cell22_2392117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2392117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392117 prefixEnd_2392117 := by exact prefixLift 2392117
  have htrace : WordTrace (prefixWord ++ tailWord_2392117) baseStart_2392117 baseEnd_2392117 := by
    simpa [prefixWord, tailWord_2392117, baseEnd_2392117] using wordTrace_append hprefix tailTrace_2392117
  have hstable : (prefixWord ++ tailWord_2392117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392117).length < 2 ^ (prefixWord ++ tailWord_2392117).sum := by decide
  have hdescent : baseEnd_2392117 < baseStart_2392117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392160 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 1, 4]
def baseStart_2392160 : Nat := 118140960795 + 2392160 * 2 ^ 59
def prefixEnd_2392160 : Nat := 4983230072969 + 3 ^ 40 * 2392160 * 2
def baseEnd_2392160 : Nat := 818885254972977264465775

theorem tailTrace_2392160 : CollatzResearch.WordTrace tailWord_2392160 prefixEnd_2392160 818885254972977264465775 := by
  unfold tailWord_2392160
  simp only [CollatzResearch.WordTrace]
  refine ⟨43624621506810171623454967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58166162009080228831273289 43624621506810171623454967)
  ·
    refine ⟨65436932260215257435182451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43624621506810171623454967 65436932260215257435182451)
    ·
      refine ⟨98155398390322886152773677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65436932260215257435182451 98155398390322886152773677)
      ·
        refine ⟨36808274396371082307290129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98155398390322886152773677 36808274396371082307290129)
        ·
          refine ⟨27606205797278311730467597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36808274396371082307290129 27606205797278311730467597)
          ·
            refine ⟨10352327173979366898925349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27606205797278311730467597 10352327173979366898925349)
            ·
              refine ⟨1941061345121131293548503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10352327173979366898925349 1941061345121131293548503)
              ·
                refine ⟨2911592017681696940322755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941061345121131293548503 2911592017681696940322755)
                ·
                  refine ⟨4367388026522545410484133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911592017681696940322755 4367388026522545410484133)
                  ·
                    refine ⟨818885254972977264465775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367388026522545410484133 818885254972977264465775)
                    ·
                      rfl

theorem cell22_2392160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_2392160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392160 prefixEnd_2392160 := by exact prefixLift 2392160
  have htrace : WordTrace (prefixWord ++ tailWord_2392160) baseStart_2392160 baseEnd_2392160 := by
    simpa [prefixWord, tailWord_2392160, baseEnd_2392160] using wordTrace_append hprefix tailTrace_2392160
  have hstable : (prefixWord ++ tailWord_2392160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392160).length < 2 ^ (prefixWord ++ tailWord_2392160).sum := by decide
  have hdescent : baseEnd_2392160 < baseStart_2392160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392201 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_2392201 : Nat := 118140960795 + 2392201 * 2 ^ 59
def prefixEnd_2392201 : Nat := 4983230072969 + 3 ^ 40 * 2392201 * 2
def baseEnd_2392201 : Nat := 818899290110866824190649

theorem tailTrace_2392201 : CollatzResearch.WordTrace tailWord_2392201 prefixEnd_2392201 818899290110866824190649 := by
  unfold tailWord_2392201
  simp only [CollatzResearch.WordTrace]
  refine ⟨87250738406471807249152457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58167158937647871499434971 87250738406471807249152457)
  ·
    refine ⟨65438053804853855436864343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87250738406471807249152457 65438053804853855436864343)
    ·
      refine ⟨98157080707280783155296515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65438053804853855436864343 98157080707280783155296515)
      ·
        refine ⟨147235621060921174732944773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98157080707280783155296515 147235621060921174732944773)
        ·
          refine ⟨27606678948922720262427145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147235621060921174732944773 27606678948922720262427145)
          ·
            refine ⟨20705009211692040196820359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27606678948922720262427145 20705009211692040196820359)
            ·
              refine ⟨31057513817538060295230539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20705009211692040196820359 31057513817538060295230539)
              ·
                refine ⟨46586270726307090442845809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31057513817538060295230539 46586270726307090442845809)
                ·
                  refine ⟨34939703044730317832134357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46586270726307090442845809 34939703044730317832134357)
                  ·
                    refine ⟨818899290110866824190649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34939703044730317832134357 818899290110866824190649)
                    ·
                      rfl

theorem cell22_2392201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_2392201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392201 prefixEnd_2392201 := by exact prefixLift 2392201
  have htrace : WordTrace (prefixWord ++ tailWord_2392201) baseStart_2392201 baseEnd_2392201 := by
    simpa [prefixWord, tailWord_2392201, baseEnd_2392201] using wordTrace_append hprefix tailTrace_2392201
  have hstable : (prefixWord ++ tailWord_2392201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392201).length < 2 ^ (prefixWord ++ tailWord_2392201).sum := by decide
  have hdescent : baseEnd_2392201 < baseStart_2392201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392222 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2392222 : Nat := 118140960795 + 2392222 * 2 ^ 59
def prefixEnd_2392222 : Nat := 4983230072969 + 3 ^ 40 * 2392222 * 2
def baseEnd_2392222 : Nat := 818906478840029769415585

theorem tailTrace_2392222 : CollatzResearch.WordTrace tailWord_2392222 prefixEnd_2392222 818906478840029769415585 := by
  unfold tailWord_2392222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906438042424465979458365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58167669559597151890444613 10906438042424465979458365)
  ·
    refine ⟨4089914265909174742296887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10906438042424465979458365 4089914265909174742296887)
    ·
      refine ⟨6134871398863762113445331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4089914265909174742296887 6134871398863762113445331)
      ·
        refine ⟨9202307098295643170167997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6134871398863762113445331 9202307098295643170167997)
        ·
          refine ⟨3450865161860866188812999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9202307098295643170167997 3450865161860866188812999)
          ·
            refine ⟨5176297742791299283219499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3450865161860866188812999 5176297742791299283219499)
            ·
              refine ⟨7764446614186948924829249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176297742791299283219499 7764446614186948924829249)
              ·
                refine ⟨5823334960640211693621937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7764446614186948924829249 5823334960640211693621937)
                ·
                  refine ⟨4367501220480158770216453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823334960640211693621937 4367501220480158770216453)
                  ·
                    refine ⟨818906478840029769415585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367501220480158770216453 818906478840029769415585)
                    ·
                      rfl

theorem cell22_2392222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2392222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392222 prefixEnd_2392222 := by exact prefixLift 2392222
  have htrace : WordTrace (prefixWord ++ tailWord_2392222) baseStart_2392222 baseEnd_2392222 := by
    simpa [prefixWord, tailWord_2392222, baseEnd_2392222] using wordTrace_append hprefix tailTrace_2392222
  have hstable : (prefixWord ++ tailWord_2392222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392222).length < 2 ^ (prefixWord ++ tailWord_2392222).sum := by decide
  have hdescent : baseEnd_2392222 < baseStart_2392222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392241 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 2, 3]
def baseStart_2392241 : Nat := 118140960795 + 2392241 * 2 ^ 59
def prefixEnd_2392241 : Nat := 4983230072969 + 3 ^ 40 * 2392241 * 2
def baseEnd_2392241 : Nat := 818912982928320053190527

theorem tailTrace_2392241 : CollatzResearch.WordTrace tailWord_2392241 prefixEnd_2392241 818912982928320053190527 := by
  unfold tailWord_2392241
  simp only [CollatzResearch.WordTrace]
  refine ⟨87252197326326894080608577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58168131550884596053739051 87252197326326894080608577)
  ·
    refine ⟨65439147994745170560456433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87252197326326894080608577 65439147994745170560456433)
    ·
      refine ⟨49079360996058877920342325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65439147994745170560456433 49079360996058877920342325)
      ·
        refine ⟨4601190093380519805032093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49079360996058877920342325 4601190093380519805032093)
        ·
          refine ⟨1725446285017694926887035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4601190093380519805032093 1725446285017694926887035)
          ·
            refine ⟨2588169427526542390330553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725446285017694926887035 2588169427526542390330553)
            ·
              refine ⟨1941127070644906792747915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588169427526542390330553 1941127070644906792747915)
              ·
                refine ⟨2911690605967360189121873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941127070644906792747915 2911690605967360189121873)
                ·
                  refine ⟨2183767954475520141841405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911690605967360189121873 2183767954475520141841405)
                  ·
                    refine ⟨818912982928320053190527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2183767954475520141841405 818912982928320053190527)
                    ·
                      rfl

theorem cell22_2392241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_2392241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392241 prefixEnd_2392241 := by exact prefixLift 2392241
  have htrace : WordTrace (prefixWord ++ tailWord_2392241) baseStart_2392241 baseEnd_2392241 := by
    simpa [prefixWord, tailWord_2392241, baseEnd_2392241] using wordTrace_append hprefix tailTrace_2392241
  have hstable : (prefixWord ++ tailWord_2392241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392241).length < 2 ^ (prefixWord ++ tailWord_2392241).sum := by decide
  have hdescent : baseEnd_2392241 < baseStart_2392241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392248 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_2392248 : Nat := 118140960795 + 2392248 * 2 ^ 59
def prefixEnd_2392248 : Nat := 4983230072969 + 3 ^ 40 * 2392248 * 2
def baseEnd_2392248 : Nat := 272971793057124789421835

theorem tailTrace_2392248 : CollatzResearch.WordTrace tailWord_2392248 prefixEnd_2392248 272971793057124789421835 := by
  unfold tailWord_2392248
  simp only [CollatzResearch.WordTrace]
  refine ⟨43626226318650767138056699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58168301758201022850742265 43626226318650767138056699)
  ·
    refine ⟨65439339477976150707085049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43626226318650767138056699 65439339477976150707085049)
    ·
      refine ⟨49079504608482113030313787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65439339477976150707085049 49079504608482113030313787)
      ·
        refine ⟨73619256912723169545470681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49079504608482113030313787 73619256912723169545470681)
        ·
          refine ⟨55214442684542377159103011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73619256912723169545470681 55214442684542377159103011)
          ·
            refine ⟨82821664026813565738654517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55214442684542377159103011 82821664026813565738654517)
            ·
              refine ⟨7764531002513771787998861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82821664026813565738654517 7764531002513771787998861)
              ·
                refine ⟨2911699125942664420499573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7764531002513771787998861 2911699125942664420499573)
                ·
                  refine ⟨272971793057124789421835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2911699125942664420499573 272971793057124789421835)
                  ·
                    rfl

theorem cell22_2392248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_2392248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392248 prefixEnd_2392248 := by exact prefixLift 2392248
  have htrace : WordTrace (prefixWord ++ tailWord_2392248) baseStart_2392248 baseEnd_2392248 := by
    simpa [prefixWord, tailWord_2392248, baseEnd_2392248] using wordTrace_append hprefix tailTrace_2392248
  have hstable : (prefixWord ++ tailWord_2392248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392248).length < 2 ^ (prefixWord ++ tailWord_2392248).sum := by decide
  have hdescent : baseEnd_2392248 < baseStart_2392248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392295 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2392295 : Nat := 118140960795 + 2392295 * 2 ^ 59
def prefixEnd_2392295 : Nat := 4983230072969 + 3 ^ 40 * 2392295 * 2
def baseEnd_2392295 : Nat := 818931468231881912340361

theorem tailTrace_2392295 : CollatzResearch.WordTrace tailWord_2392295 prefixEnd_2392295 818931468231881912340361 := by
  unfold tailWord_2392295
  simp only [CollatzResearch.WordTrace]
  refine ⟨87254166868131261303074339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58169444578754174202049559 87254166868131261303074339)
  ·
    refine ⟨130881250302196891954611509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87254166868131261303074339 130881250302196891954611509)
    ·
      refine ⟨12270117215830958620744829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130881250302196891954611509 12270117215830958620744829)
      ·
        refine ⟨4601293955936609482779311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12270117215830958620744829 4601293955936609482779311)
        ·
          refine ⟨6901940933904914224168967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4601293955936609482779311 6901940933904914224168967)
          ·
            refine ⟨10352911400857371336253451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901940933904914224168967 10352911400857371336253451)
            ·
              refine ⟨15529367101286057004380177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10352911400857371336253451 15529367101286057004380177)
              ·
                refine ⟨11647025325964542753285133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15529367101286057004380177 11647025325964542753285133)
                ·
                  refine ⟨4367634497236703532481925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11647025325964542753285133 4367634497236703532481925)
                  ·
                    refine ⟨818931468231881912340361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367634497236703532481925 818931468231881912340361)
                    ·
                      rfl

theorem cell22_2392295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2392295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392295 prefixEnd_2392295 := by exact prefixLift 2392295
  have htrace : WordTrace (prefixWord ++ tailWord_2392295) baseStart_2392295 baseEnd_2392295 := by
    simpa [prefixWord, tailWord_2392295, baseEnd_2392295] using wordTrace_append hprefix tailTrace_2392295
  have hstable : (prefixWord ++ tailWord_2392295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392295).length < 2 ^ (prefixWord ++ tailWord_2392295).sum := by decide
  have hdescent : baseEnd_2392295 < baseStart_2392295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392323 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 1, 6]
def baseStart_2392323 : Nat := 118140960795 + 2392323 * 2 ^ 59
def prefixEnd_2392323 : Nat := 4983230072969 + 3 ^ 40 * 2392323 * 2
def baseEnd_2392323 : Nat := 818941053204099172640275

theorem tailTrace_2392323 : CollatzResearch.WordTrace tailWord_2392323 prefixEnd_2392323 818941053204099172640275 := by
  unfold tailWord_2392323
  simp only [CollatzResearch.WordTrace]
  refine ⟨87255188112029822085093623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58170125408019881390062415 87255188112029822085093623)
  ·
    refine ⟨130882782168044733127640435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87255188112029822085093623 130882782168044733127640435)
    ·
      refine ⟨196324173252067099691460653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130882782168044733127640435 196324173252067099691460653)
      ·
        refine ⟨73621564969525162384297745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196324173252067099691460653 73621564969525162384297745)
        ·
          refine ⟨55216173727143871788223309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73621564969525162384297745 55216173727143871788223309)
          ·
            refine ⟨20706065147678951920583741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55216173727143871788223309 20706065147678951920583741)
            ·
              refine ⟨7764774430379606970218903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20706065147678951920583741 7764774430379606970218903)
              ·
                refine ⟨11647161645569410455328355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7764774430379606970218903 11647161645569410455328355)
                ·
                  refine ⟨17470742468354115682992533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11647161645569410455328355 17470742468354115682992533)
                  ·
                    refine ⟨818941053204099172640275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17470742468354115682992533 818941053204099172640275)
                    ·
                      rfl

theorem cell22_2392323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_2392323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392323 prefixEnd_2392323 := by exact prefixLift 2392323
  have htrace : WordTrace (prefixWord ++ tailWord_2392323) baseStart_2392323 baseEnd_2392323 := by
    simpa [prefixWord, tailWord_2392323, baseEnd_2392323] using wordTrace_append hprefix tailTrace_2392323
  have hstable : (prefixWord ++ tailWord_2392323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392323).length < 2 ^ (prefixWord ++ tailWord_2392323).sum := by decide
  have hdescent : baseEnd_2392323 < baseStart_2392323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392372 : List Nat := [2, 5, 1, 1, 1, 2, 4, 6]
def baseStart_2392372 : Nat := 118140960795 + 2392372 * 2 ^ 59
def prefixEnd_2392372 : Nat := 4983230072969 + 3 ^ 40 * 2392372 * 2
def baseEnd_2392372 : Nat := 90995314100608819796125

theorem tailTrace_2392372 : CollatzResearch.WordTrace tailWord_2392372 prefixEnd_2392372 90995314100608819796125 := by
  unfold tailWord_2392372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43628487644426151726813685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58171316859234868969084913 43628487644426151726813685)
  ·
    refine ⟨4090170716664951724388783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43628487644426151726813685 4090170716664951724388783)
    ·
      refine ⟨6135256074997427586583175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4090170716664951724388783 6135256074997427586583175)
      ·
        refine ⟨9202884112496141379874763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135256074997427586583175 9202884112496141379874763)
        ·
          refine ⟨13804326168744212069812145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202884112496141379874763 13804326168744212069812145)
          ·
            refine ⟨10353244626558159052359109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13804326168744212069812145 10353244626558159052359109)
            ·
              refine ⟨1941233367479654822317333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10353244626558159052359109 1941233367479654822317333)
              ·
                refine ⟨90995314100608819796125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1941233367479654822317333 90995314100608819796125)
                ·
                  rfl

theorem cell22_2392372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 6].length) (baseStart_2392372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392372 prefixEnd_2392372 := by exact prefixLift 2392372
  have htrace : WordTrace (prefixWord ++ tailWord_2392372) baseStart_2392372 baseEnd_2392372 := by
    simpa [prefixWord, tailWord_2392372, baseEnd_2392372] using wordTrace_append hprefix tailTrace_2392372
  have hstable : (prefixWord ++ tailWord_2392372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392372).length < 2 ^ (prefixWord ++ tailWord_2392372).sum := by decide
  have hdescent : baseEnd_2392372 < baseStart_2392372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392383 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 9]
def baseStart_2392383 : Nat := 118140960795 + 2392383 * 2 ^ 59
def prefixEnd_2392383 : Nat := 4983230072969 + 3 ^ 40 * 2392383 * 2
def baseEnd_2392383 : Nat := 272987197476759672046697

theorem tailTrace_2392383 : CollatzResearch.WordTrace tailWord_2392383 prefixEnd_2392383 272987197476759672046697 := by
  unfold tailWord_2392383
  simp only [CollatzResearch.WordTrace]
  refine ⟨87257376491812452332277803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58171584327874968221518535 87257376491812452332277803)
  ·
    refine ⟨130886064737718678498416705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87257376491812452332277803 130886064737718678498416705)
    ·
      refine ⟨98164548553289008873812529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130886064737718678498416705 98164548553289008873812529)
      ·
        refine ⟨73623411414966756655359397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98164548553289008873812529 73623411414966756655359397)
        ·
          refine ⟨13804389640306266872879887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73623411414966756655359397 13804389640306266872879887)
          ·
            refine ⟨20706584460459400309319831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13804389640306266872879887 20706584460459400309319831)
            ·
              refine ⟨31059876690689100463979747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20706584460459400309319831 31059876690689100463979747)
              ·
                refine ⟨46589815036033650695969621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31059876690689100463979747 46589815036033650695969621)
                ·
                  refine ⟨272987197476759672046697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46589815036033650695969621 272987197476759672046697)
                  ·
                    rfl

theorem cell22_2392383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_2392383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392383 prefixEnd_2392383 := by exact prefixLift 2392383
  have htrace : WordTrace (prefixWord ++ tailWord_2392383) baseStart_2392383 baseEnd_2392383 := by
    simpa [prefixWord, tailWord_2392383, baseEnd_2392383] using wordTrace_append hprefix tailTrace_2392383
  have hstable : (prefixWord ++ tailWord_2392383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392383).length < 2 ^ (prefixWord ++ tailWord_2392383).sum := by decide
  have hdescent : baseEnd_2392383 < baseStart_2392383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392404 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2392404 : Nat := 118140960795 + 2392404 * 2 ^ 59
def prefixEnd_2392404 : Nat := 4983230072969 + 3 ^ 40 * 2392404 * 2
def baseEnd_2392404 : Nat := 818968781159441961365027

theorem tailTrace_2392404 : CollatzResearch.WordTrace tailWord_2392404 prefixEnd_2392404 818968781159441961365027 := by
  unfold tailWord_2392404
  simp only [CollatzResearch.WordTrace]
  refine ⟨43629071212368186459396133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58172094949824248612528177 43629071212368186459396133)
  ·
    refine ⟨8180450852319034961136775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43629071212368186459396133 8180450852319034961136775)
    ·
      refine ⟨12270676278478552441705163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8180450852319034961136775 12270676278478552441705163)
      ·
        refine ⟨18406014417717828662557745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12270676278478552441705163 18406014417717828662557745)
        ·
          refine ⟨13804510813288371496918309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18406014417717828662557745 13804510813288371496918309)
          ·
            refine ⟨2588345777491569655672183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13804510813288371496918309 2588345777491569655672183)
            ·
              refine ⟨3882518666237354483508275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588345777491569655672183 3882518666237354483508275)
              ·
                refine ⟨5823777999356031725262413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882518666237354483508275 5823777999356031725262413)
                ·
                  refine ⟨2183916749758511896973405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5823777999356031725262413 2183916749758511896973405)
                  ·
                    refine ⟨818968781159441961365027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2183916749758511896973405 818968781159441961365027)
                    ·
                      rfl

theorem cell22_2392404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2392404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392404 prefixEnd_2392404 := by exact prefixLift 2392404
  have htrace : WordTrace (prefixWord ++ tailWord_2392404) baseStart_2392404 baseEnd_2392404 := by
    simpa [prefixWord, tailWord_2392404, baseEnd_2392404] using wordTrace_append hprefix tailTrace_2392404
  have hstable : (prefixWord ++ tailWord_2392404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392404).length < 2 ^ (prefixWord ++ tailWord_2392404).sum := by decide
  have hdescent : baseEnd_2392404 < baseStart_2392404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392627 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 2, 4]
def baseStart_2392627 : Nat := 118140960795 + 2392627 * 2 ^ 59
def prefixEnd_2392627 : Nat := 4983230072969 + 3 ^ 40 * 2392627 * 2
def baseEnd_2392627 : Nat := 819045118616743713039343

theorem tailTrace_2392627 : CollatzResearch.WordTrace tailWord_2392627 prefixEnd_2392627 819045118616743713039343 := by
  unfold tailWord_2392627
  simp only [CollatzResearch.WordTrace]
  refine ⟨87266275902928482004160135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58177517268618988002773423 87266275902928482004160135)
  ·
    refine ⟨130899413854392723006240203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87266275902928482004160135 130899413854392723006240203)
    ·
      refine ⟨196349120781589084509360305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130899413854392723006240203 196349120781589084509360305)
      ·
        refine ⟨147261840586191813382020229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196349120781589084509360305 147261840586191813382020229)
        ·
          refine ⟨27611595109910965009128793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147261840586191813382020229 27611595109910965009128793)
          ·
            refine ⟨20708696332433223756846595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27611595109910965009128793 20708696332433223756846595)
            ·
              refine ⟨31063044498649835635269893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20708696332433223756846595 31063044498649835635269893)
              ·
                refine ⟨5824320843496844181613105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31063044498649835635269893 5824320843496844181613105)
                ·
                  refine ⟨4368240632622633136209829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5824320843496844181613105 4368240632622633136209829)
                  ·
                    refine ⟨819045118616743713039343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368240632622633136209829 819045118616743713039343)
                    ·
                      rfl

theorem cell22_2392627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_2392627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392627 prefixEnd_2392627 := by exact prefixLift 2392627
  have htrace : WordTrace (prefixWord ++ tailWord_2392627) baseStart_2392627 baseEnd_2392627 := by
    simpa [prefixWord, tailWord_2392627, baseEnd_2392627] using wordTrace_append hprefix tailTrace_2392627
  have hstable : (prefixWord ++ tailWord_2392627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392627).length < 2 ^ (prefixWord ++ tailWord_2392627).sum := by decide
  have hdescent : baseEnd_2392627 < baseStart_2392627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392646 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2392646 : Nat := 118140960795 + 2392646 * 2 ^ 59
def prefixEnd_2392646 : Nat := 4983230072969 + 3 ^ 40 * 2392646 * 2
def baseEnd_2392646 : Nat := 819051622705033996814285

theorem tailTrace_2392646 : CollatzResearch.WordTrace tailWord_2392646 prefixEnd_2392646 819051622705033996814285 := by
  unfold tailWord_2392646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2727092777808114007784431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58177979259906432166067861 2727092777808114007784431)
  ·
    refine ⟨4090639166712171011676647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2727092777808114007784431 4090639166712171011676647)
    ·
      refine ⟨6135958750068256517514971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4090639166712171011676647 6135958750068256517514971)
      ·
        refine ⟨9203938125102384776272457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135958750068256517514971 9203938125102384776272457)
        ·
          refine ⟨6902953593826788582204343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9203938125102384776272457 6902953593826788582204343)
          ·
            refine ⟨10354430390740182873306515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6902953593826788582204343 10354430390740182873306515)
            ·
              refine ⟨15531645586110274309959773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10354430390740182873306515 15531645586110274309959773)
              ·
                refine ⟨5824367094791352866234915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15531645586110274309959773 5824367094791352866234915)
                ·
                  refine ⟨8736550642187029299352373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5824367094791352866234915 8736550642187029299352373)
                  ·
                    refine ⟨819051622705033996814285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8736550642187029299352373 819051622705033996814285)
                    ·
                      rfl

theorem cell22_2392646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2392646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392646 prefixEnd_2392646 := by exact prefixLift 2392646
  have htrace : WordTrace (prefixWord ++ tailWord_2392646) baseStart_2392646 baseEnd_2392646 := by
    simpa [prefixWord, tailWord_2392646, baseEnd_2392646] using wordTrace_append hprefix tailTrace_2392646
  have hstable : (prefixWord ++ tailWord_2392646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392646).length < 2 ^ (prefixWord ++ tailWord_2392646).sum := by decide
  have hdescent : baseEnd_2392646 < baseStart_2392646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392680 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 2, 3]
def baseStart_2392680 : Nat := 118140960795 + 2392680 * 2 ^ 59
def prefixEnd_2392680 : Nat := 4983230072969 + 3 ^ 40 * 2392680 * 2
def baseEnd_2392680 : Nat := 819063261599869241464181

theorem tailTrace_2392680 : CollatzResearch.WordTrace tailWord_2392680 prefixEnd_2392680 819063261599869241464181 := by
  unfold tailWord_2392680
  simp only [CollatzResearch.WordTrace]
  refine ⟨43634104485868236027919747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58178805981157648037226329 43634104485868236027919747)
  ·
    refine ⟨65451156728802354041879621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43634104485868236027919747 65451156728802354041879621)
    ·
      refine ⟨12272091886650441382852429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65451156728802354041879621 12272091886650441382852429)
      ·
        refine ⟨4602034457493915518569661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12272091886650441382852429 4602034457493915518569661)
        ·
          refine ⟨1725762921560218319463623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4602034457493915518569661 1725762921560218319463623)
          ·
            refine ⟨2588644382340327479195435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725762921560218319463623 2588644382340327479195435)
            ·
              refine ⟨3882966573510491218793153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588644382340327479195435 3882966573510491218793153)
              ·
                refine ⟨2912224930132868414094865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3882966573510491218793153 2912224930132868414094865)
                ·
                  refine ⟨2184168697599651310571149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912224930132868414094865 2184168697599651310571149)
                  ·
                    refine ⟨819063261599869241464181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184168697599651310571149 819063261599869241464181)
                    ·
                      rfl

theorem cell22_2392680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_2392680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392680 prefixEnd_2392680 := by exact prefixLift 2392680
  have htrace : WordTrace (prefixWord ++ tailWord_2392680) baseStart_2392680 baseEnd_2392680 := by
    simpa [prefixWord, tailWord_2392680, baseEnd_2392680] using wordTrace_append hprefix tailTrace_2392680
  have hstable : (prefixWord ++ tailWord_2392680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392680).length < 2 ^ (prefixWord ++ tailWord_2392680).sum := by decide
  have hdescent : baseEnd_2392680 < baseStart_2392680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392764 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2392764 : Nat := 118140960795 + 2392764 * 2 ^ 59
def prefixEnd_2392764 : Nat := 4983230072969 + 3 ^ 40 * 2392764 * 2
def baseEnd_2392764 : Nat := 819092016516521022363923

theorem tailTrace_2392764 : CollatzResearch.WordTrace tailWord_2392764 prefixEnd_2392764 819092016516521022363923 := by
  unfold tailWord_2392764
  simp only [CollatzResearch.WordTrace]
  refine ⟨43635636351716077200948673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58180848468954769601264897 43635636351716077200948673)
  ·
    refine ⟨32726727263787057900711505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43635636351716077200948673 32726727263787057900711505)
    ·
      refine ⟨24545045447840293425533629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32726727263787057900711505 24545045447840293425533629)
      ·
        refine ⟨9204392042940110034575111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24545045447840293425533629 9204392042940110034575111)
        ·
          refine ⟨13806588064410165051862667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9204392042940110034575111 13806588064410165051862667)
          ·
            refine ⟨20709882096615247577794001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13806588064410165051862667 20709882096615247577794001)
            ·
              refine ⟨15532411572461435683345501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20709882096615247577794001 15532411572461435683345501)
              ·
                refine ⟨5824654339673038381254563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15532411572461435683345501 5824654339673038381254563)
                ·
                  refine ⟨8736981509509557571881845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5824654339673038381254563 8736981509509557571881845)
                  ·
                    refine ⟨819092016516521022363923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8736981509509557571881845 819092016516521022363923)
                    ·
                      rfl

theorem cell22_2392764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2392764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392764 prefixEnd_2392764 := by exact prefixLift 2392764
  have htrace : WordTrace (prefixWord ++ tailWord_2392764) baseStart_2392764 baseEnd_2392764 := by
    simpa [prefixWord, tailWord_2392764, baseEnd_2392764] using wordTrace_append hprefix tailTrace_2392764
  have hstable : (prefixWord ++ tailWord_2392764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392764).length < 2 ^ (prefixWord ++ tailWord_2392764).sum := by decide
  have hdescent : baseEnd_2392764 < baseStart_2392764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392894 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_2392894 : Nat := 118140960795 + 2392894 * 2 ^ 59
def prefixEnd_2392894 : Nat := 4983230072969 + 3 ^ 40 * 2392894 * 2
def baseEnd_2392894 : Nat := 819136518173244016613525

theorem tailTrace_2392894 : CollatzResearch.WordTrace tailWord_2392894 prefixEnd_2392894 819136518173244016613525 := by
  unfold tailWord_2392894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909501774120148325516217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58184009461974124402753157 10909501774120148325516217)
  ·
    refine ⟨8182126330590111244137163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10909501774120148325516217 8182126330590111244137163)
    ·
      refine ⟨12273189495885166866205745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8182126330590111244137163 12273189495885166866205745)
      ·
        refine ⟨9204892121913875149654309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12273189495885166866205745 9204892121913875149654309)
        ·
          refine ⟨1725917272858851590560183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9204892121913875149654309 1725917272858851590560183)
          ·
            refine ⟨2588875909288277385840275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725917272858851590560183 2588875909288277385840275)
            ·
              refine ⟨3883313863932416078760413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588875909288277385840275 3883313863932416078760413)
              ·
                refine ⟨1456242698974656029535155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3883313863932416078760413 1456242698974656029535155)
                ·
                  refine ⟨2184364048461984044302733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456242698974656029535155 2184364048461984044302733)
                  ·
                    refine ⟨819136518173244016613525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184364048461984044302733 819136518173244016613525)
                    ·
                      rfl

theorem cell22_2392894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_2392894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392894 prefixEnd_2392894 := by exact prefixLift 2392894
  have htrace : WordTrace (prefixWord ++ tailWord_2392894) baseStart_2392894 baseEnd_2392894 := by
    simpa [prefixWord, tailWord_2392894, baseEnd_2392894] using wordTrace_append hprefix tailTrace_2392894
  have hstable : (prefixWord ++ tailWord_2392894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392894).length < 2 ^ (prefixWord ++ tailWord_2392894).sum := by decide
  have hdescent : baseEnd_2392894 < baseStart_2392894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392899 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_2392899 : Nat := 118140960795 + 2392899 * 2 ^ 59
def prefixEnd_2392899 : Nat := 4983230072969 + 3 ^ 40 * 2392899 * 2
def baseEnd_2392899 : Nat := 819138229775425670238509

theorem tailTrace_2392899 : CollatzResearch.WordTrace tailWord_2392899 prefixEnd_2392899 819138229775425670238509 := by
  unfold tailWord_2392899
  simp only [CollatzResearch.WordTrace]
  refine ⟨87276196557943072458061751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58184131038628714972041167 87276196557943072458061751)
  ·
    refine ⟨130914294836914608687092627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87276196557943072458061751 130914294836914608687092627)
    ·
      refine ⟨196371442255371913030638941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130914294836914608687092627 196371442255371913030638941)
      ·
        refine ⟨73639290845764467386489603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196371442255371913030638941 73639290845764467386489603)
        ·
          refine ⟨110458936268646701079734405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73639290845764467386489603 110458936268646701079734405)
          ·
            refine ⟨20711050550371256452450201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110458936268646701079734405 20711050550371256452450201)
            ·
              refine ⟨15533287912778442339337651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20711050550371256452450201 15533287912778442339337651)
              ·
                refine ⟨23299931869167663509006477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15533287912778442339337651 23299931869167663509006477)
                ·
                  refine ⟨8737474450937873815877429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23299931869167663509006477 8737474450937873815877429)
                  ·
                    refine ⟨819138229775425670238509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8737474450937873815877429 819138229775425670238509)
                    ·
                      rfl

theorem cell22_2392899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_2392899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392899 prefixEnd_2392899 := by exact prefixLift 2392899
  have htrace : WordTrace (prefixWord ++ tailWord_2392899) baseStart_2392899 baseEnd_2392899 := by
    simpa [prefixWord, tailWord_2392899, baseEnd_2392899] using wordTrace_append hprefix tailTrace_2392899
  have hstable : (prefixWord ++ tailWord_2392899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392899).length < 2 ^ (prefixWord ++ tailWord_2392899).sum := by decide
  have hdescent : baseEnd_2392899 < baseStart_2392899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392901 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 4]
def baseStart_2392901 : Nat := 118140960795 + 2392901 * 2 ^ 59
def prefixEnd_2392901 : Nat := 4983230072969 + 3 ^ 40 * 2392901 * 2
def baseEnd_2392901 : Nat := 273046304805432777229501

theorem tailTrace_2392901 : CollatzResearch.WordTrace tailWord_2392901 prefixEnd_2392901 273046304805432777229501 := by
  unfold tailWord_2392901
  simp only [CollatzResearch.WordTrace]
  refine ⟨87276269503935826799634557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58184179669290551199756371 87276269503935826799634557)
  ·
    refine ⟨32728601063975935049862959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87276269503935826799634557 32728601063975935049862959)
    ·
      refine ⟨49092901595963902574794439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32728601063975935049862959 49092901595963902574794439)
      ·
        refine ⟨73639352393945853862191659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49092901595963902574794439 73639352393945853862191659)
        ·
          refine ⟨110459028590918780793287489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73639352393945853862191659 110459028590918780793287489)
          ·
            refine ⟨82844271443189085594965617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110459028590918780793287489 82844271443189085594965617)
            ·
              refine ⟨62133203582391814196224213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82844271443189085594965617 62133203582391814196224213)
              ·
                refine ⟨1456246958962308145224005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62133203582391814196224213 1456246958962308145224005)
                ·
                  refine ⟨273046304805432777229501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456246958962308145224005 273046304805432777229501)
                  ·
                    rfl

theorem cell22_2392901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_2392901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392901 prefixEnd_2392901 := by exact prefixLift 2392901
  have htrace : WordTrace (prefixWord ++ tailWord_2392901) baseStart_2392901 baseEnd_2392901 := by
    simpa [prefixWord, tailWord_2392901, baseEnd_2392901] using wordTrace_append hprefix tailTrace_2392901
  have hstable : (prefixWord ++ tailWord_2392901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392901).length < 2 ^ (prefixWord ++ tailWord_2392901).sum := by decide
  have hdescent : baseEnd_2392901 < baseStart_2392901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392944 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_2392944 : Nat := 118140960795 + 2392944 * 2 ^ 59
def prefixEnd_2392944 : Nat := 4983230072969 + 3 ^ 40 * 2392944 * 2
def baseEnd_2392944 : Nat := 819153634195060552863371

theorem tailTrace_2392944 : CollatzResearch.WordTrace tailWord_2392944 prefixEnd_2392944 819153634195060552863371 := by
  unfold tailWord_2392944
  simp only [CollatzResearch.WordTrace]
  refine ⟨43638918921390022571724943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58185225228520030095633257 43638918921390022571724943)
  ·
    refine ⟨65458378382085033857587415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43638918921390022571724943 65458378382085033857587415)
    ·
      refine ⟨98187567573127550786381123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65458378382085033857587415 98187567573127550786381123)
      ·
        refine ⟨147281351359691326179571685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98187567573127550786381123 147281351359691326179571685)
        ·
          refine ⟨27615253379942123658669691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147281351359691326179571685 27615253379942123658669691)
          ·
            refine ⟨41422880069913185488004537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27615253379942123658669691 41422880069913185488004537)
            ·
              refine ⟨31067160052434889116003403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41422880069913185488004537 31067160052434889116003403)
              ·
                refine ⟨46600740078652333674005105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31067160052434889116003403 46600740078652333674005105)
                ·
                  refine ⟨34950555058989250255503829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46600740078652333674005105 34950555058989250255503829)
                  ·
                    refine ⟨819153634195060552863371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34950555058989250255503829 819153634195060552863371)
                    ·
                      rfl

theorem cell22_2392944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_2392944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2392944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2392944 prefixEnd_2392944 := by exact prefixLift 2392944
  have htrace : WordTrace (prefixWord ++ tailWord_2392944) baseStart_2392944 baseEnd_2392944 := by
    simpa [prefixWord, tailWord_2392944, baseEnd_2392944] using wordTrace_append hprefix tailTrace_2392944
  have hstable : (prefixWord ++ tailWord_2392944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392944).length < 2 ^ (prefixWord ++ tailWord_2392944).sum := by decide
  have hdescent : baseEnd_2392944 < baseStart_2392944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393053 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 6]
def baseStart_2393053 : Nat := 118140960795 + 2393053 * 2 ^ 59
def prefixEnd_2393053 : Nat := 4983230072969 + 3 ^ 40 * 2393053 * 2
def baseEnd_2393053 : Nat := 273063649040873533962679

theorem tailTrace_2393053 : CollatzResearch.WordTrace tailWord_2393053 prefixEnd_2393053 273063649040873533962679 := by
  unfold tailWord_2393053
  simp only [CollatzResearch.WordTrace]
  refine ⟨87281813399385156759167813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58187875599590104506111875 87281813399385156759167813)
  ·
    refine ⟨16365340012384716892343965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87281813399385156759167813 16365340012384716892343965)
    ·
      refine ⟨6137002504644268834628987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16365340012384716892343965 6137002504644268834628987)
      ·
        refine ⟨9205503756966403251943481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6137002504644268834628987 9205503756966403251943481)
        ·
          refine ⟨6904127817724802438957611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9205503756966403251943481 6904127817724802438957611)
          ·
            refine ⟨10356191726587203658436417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904127817724802438957611 10356191726587203658436417)
            ·
              refine ⟨7767143794940402743827313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10356191726587203658436417 7767143794940402743827313)
              ·
                refine ⟨5825357846205302057870485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7767143794940402743827313 5825357846205302057870485)
                ·
                  refine ⟨273063649040873533962679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5825357846205302057870485 273063649040873533962679)
                  ·
                    rfl

theorem cell22_2393053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_2393053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393053 prefixEnd_2393053 := by exact prefixLift 2393053
  have htrace : WordTrace (prefixWord ++ tailWord_2393053) baseStart_2393053 baseEnd_2393053 := by
    simpa [prefixWord, tailWord_2393053, baseEnd_2393053] using wordTrace_append hprefix tailTrace_2393053
  have hstable : (prefixWord ++ tailWord_2393053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393053).length < 2 ^ (prefixWord ++ tailWord_2393053).sum := by decide
  have hdescent : baseEnd_2393053 < baseStart_2393053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393055 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 1, 4]
def baseStart_2393055 : Nat := 118140960795 + 2393055 * 2 ^ 59
def prefixEnd_2393055 : Nat := 4983230072969 + 3 ^ 40 * 2393055 * 2
def baseEnd_2393055 : Nat := 819191631763493263338031

theorem tailTrace_2393055 : CollatzResearch.WordTrace tailWord_2393055 prefixEnd_2393055 819191631763493263338031 := by
  unfold tailWord_2393055
  simp only [CollatzResearch.WordTrace]
  refine ⟨87281886345377911100740619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58187924230251940733827079 87281886345377911100740619)
  ·
    refine ⟨130922829518066866651110929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87281886345377911100740619 130922829518066866651110929)
    ·
      refine ⟨98192122138550149988333197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130922829518066866651110929 98192122138550149988333197)
      ·
        refine ⟨36822045801956306245624949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98192122138550149988333197 36822045801956306245624949)
        ·
          refine ⟨3452066793933403710527339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36822045801956306245624949 3452066793933403710527339)
          ·
            refine ⟨5178100190900105565791009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452066793933403710527339 5178100190900105565791009)
            ·
              refine ⟨3883575143175079174343257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178100190900105565791009 3883575143175079174343257)
              ·
                refine ⟨2912681357381309380757443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3883575143175079174343257 2912681357381309380757443)
                ·
                  refine ⟨4369022036071964071136165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912681357381309380757443 4369022036071964071136165)
                  ·
                    refine ⟨819191631763493263338031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369022036071964071136165 819191631763493263338031)
                    ·
                      rfl

theorem cell22_2393055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_2393055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393055 prefixEnd_2393055 := by exact prefixLift 2393055
  have htrace : WordTrace (prefixWord ++ tailWord_2393055) baseStart_2393055 baseEnd_2393055 := by
    simpa [prefixWord, tailWord_2393055, baseEnd_2393055] using wordTrace_append hprefix tailTrace_2393055
  have hstable : (prefixWord ++ tailWord_2393055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393055).length < 2 ^ (prefixWord ++ tailWord_2393055).sum := by decide
  have hdescent : baseEnd_2393055 < baseStart_2393055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393098 : List Nat := [3, 1, 2, 2, 3, 2, 2, 7]
def baseStart_2393098 : Nat := 118140960795 + 2393098 * 2 ^ 59
def prefixEnd_2393098 : Nat := 4983230072969 + 3 ^ 40 * 2393098 * 2
def baseEnd_2393098 : Nat := 91022927949139498279211

theorem tailTrace_2393098 : CollatzResearch.WordTrace tailWord_2393098 prefixEnd_2393098 91022927949139498279211 := by
  unfold tailWord_2393098
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820863671055532361138987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58188969789481419629703965 21820863671055532361138987)
  ·
    refine ⟨32731295506583298541708481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21820863671055532361138987 32731295506583298541708481)
    ·
      refine ⟨24548471629937473906281361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32731295506583298541708481 24548471629937473906281361)
      ·
        refine ⟨18411353722453105429711021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24548471629937473906281361 18411353722453105429711021)
        ·
          refine ⟨6904257645919914536141633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18411353722453105429711021 6904257645919914536141633)
          ·
            refine ⟨5178193234439935902106225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6904257645919914536141633 5178193234439935902106225)
            ·
              refine ⟨3883644925829951926579669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178193234439935902106225 3883644925829951926579669)
              ·
                refine ⟨91022927949139498279211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3883644925829951926579669 91022927949139498279211)
                ·
                  rfl

theorem cell22_2393098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_2393098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393098 prefixEnd_2393098 := by exact prefixLift 2393098
  have htrace : WordTrace (prefixWord ++ tailWord_2393098) baseStart_2393098 baseEnd_2393098 := by
    simpa [prefixWord, tailWord_2393098, baseEnd_2393098] using wordTrace_append hprefix tailTrace_2393098
  have hstable : (prefixWord ++ tailWord_2393098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393098).length < 2 ^ (prefixWord ++ tailWord_2393098).sum := by decide
  have hdescent : baseEnd_2393098 < baseStart_2393098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393102 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_2393102 : Nat := 118140960795 + 2393102 * 2 ^ 59
def prefixEnd_2393102 : Nat := 4983230072969 + 3 ^ 40 * 2393102 * 2
def baseEnd_2393102 : Nat := 819207720824000807412887

theorem tailTrace_2393102 : CollatzResearch.WordTrace tailWord_2393102 prefixEnd_2393102 819207720824000807412887 := by
  unfold tailWord_2393102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910450072025954765962695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58189067050805092085134373 10910450072025954765962695)
  ·
    refine ⟨16365675108038932148944043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10910450072025954765962695 16365675108038932148944043)
    ·
      refine ⟨24548512662058398223416065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16365675108038932148944043 24548512662058398223416065)
      ·
        refine ⟨18411384496543798667562049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24548512662058398223416065 18411384496543798667562049)
        ·
          refine ⟨13808538372407849000671537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18411384496543798667562049 13808538372407849000671537)
          ·
            refine ⟨10356403779305886750503653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13808538372407849000671537 10356403779305886750503653)
            ·
              refine ⟨1941825708619853765719435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10356403779305886750503653 1941825708619853765719435)
              ·
                refine ⟨2912738562929780648579153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941825708619853765719435 2912738562929780648579153)
                ·
                  refine ⟨2184553922197335486434365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912738562929780648579153 2184553922197335486434365)
                  ·
                    refine ⟨819207720824000807412887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184553922197335486434365 819207720824000807412887)
                    ·
                      rfl

theorem cell22_2393102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_2393102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393102 prefixEnd_2393102 := by exact prefixLift 2393102
  have htrace : WordTrace (prefixWord ++ tailWord_2393102) baseStart_2393102 baseEnd_2393102 := by
    simpa [prefixWord, tailWord_2393102, baseEnd_2393102] using wordTrace_append hprefix tailTrace_2393102
  have hstable : (prefixWord ++ tailWord_2393102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393102).length < 2 ^ (prefixWord ++ tailWord_2393102).sum := by decide
  have hdescent : baseEnd_2393102 < baseStart_2393102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393106 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2393106 : Nat := 118140960795 + 2393106 * 2 ^ 59
def prefixEnd_2393106 : Nat := 4983230072969 + 3 ^ 40 * 2393106 * 2
def baseEnd_2393106 : Nat := 819209090105746130312875

theorem tailTrace_2393106 : CollatzResearch.WordTrace tailWord_2393106 prefixEnd_2393106 819209090105746130312875 := by
  unfold tailWord_2393106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820936617048286702711793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58189164312128764540564781 21820936617048286702711793)
  ·
    refine ⟨16365702462786215027033845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21820936617048286702711793 16365702462786215027033845)
    ·
      refine ⟨1534284605886207658784423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16365702462786215027033845 1534284605886207658784423)
      ·
        refine ⟨2301426908829311488176635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534284605886207658784423 2301426908829311488176635)
        ·
          refine ⟨3452140363243967232264953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301426908829311488176635 3452140363243967232264953)
          ·
            refine ⟨2589105272432975424198715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3452140363243967232264953 2589105272432975424198715)
            ·
              refine ⟨3883657908649463136298073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589105272432975424198715 3883657908649463136298073)
              ·
                refine ⟨2912743431487097352223555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3883657908649463136298073 2912743431487097352223555)
                ·
                  refine ⟨4369115147230646028335333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912743431487097352223555 4369115147230646028335333)
                  ·
                    refine ⟨819209090105746130312875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369115147230646028335333 819209090105746130312875)
                    ·
                      rfl

theorem cell22_2393106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2393106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393106 prefixEnd_2393106 := by exact prefixLift 2393106
  have htrace : WordTrace (prefixWord ++ tailWord_2393106) baseStart_2393106 baseEnd_2393106 := by
    simpa [prefixWord, tailWord_2393106, baseEnd_2393106] using wordTrace_append hprefix tailTrace_2393106
  have hstable : (prefixWord ++ tailWord_2393106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393106).length < 2 ^ (prefixWord ++ tailWord_2393106).sum := by decide
  have hdescent : baseEnd_2393106 < baseStart_2393106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393113 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_2393113 : Nat := 118140960795 + 2393113 * 2 ^ 59
def prefixEnd_2393113 : Nat := 4983230072969 + 3 ^ 40 * 2393113 * 2
def baseEnd_2393113 : Nat := 819211486348800445387853

theorem tailTrace_2393113 : CollatzResearch.WordTrace tailWord_2393113 prefixEnd_2393113 819211486348800445387853 := by
  unfold tailWord_2393113
  simp only [CollatzResearch.WordTrace]
  refine ⟨87284001779167787006351993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58189334519445191337567995 87284001779167787006351993)
  ·
    refine ⟨65463001334375840254763995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87284001779167787006351993 65463001334375840254763995)
    ·
      refine ⟨98194502001563760382145993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65463001334375840254763995 98194502001563760382145993)
      ·
        refine ⟨73645876501172820286609495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98194502001563760382145993 73645876501172820286609495)
        ·
          refine ⟨110468814751759230429914243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73645876501172820286609495 110468814751759230429914243)
          ·
            refine ⟨165703222127638845644871365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110468814751759230429914243 165703222127638845644871365)
            ·
              refine ⟨31069354148932283558413381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165703222127638845644871365 31069354148932283558413381)
              ·
                refine ⟨5825503902924803167202509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31069354148932283558413381 5825503902924803167202509)
                ·
                  refine ⟨2184563963596801187700941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5825503902924803167202509 2184563963596801187700941)
                  ·
                    refine ⟨819211486348800445387853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184563963596801187700941 819211486348800445387853)
                    ·
                      rfl

theorem cell22_2393113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_2393113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393113 prefixEnd_2393113 := by exact prefixLift 2393113
  have htrace : WordTrace (prefixWord ++ tailWord_2393113) baseStart_2393113 baseEnd_2393113 := by
    simpa [prefixWord, tailWord_2393113, baseEnd_2393113] using wordTrace_append hprefix tailTrace_2393113
  have hstable : (prefixWord ++ tailWord_2393113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393113).length < 2 ^ (prefixWord ++ tailWord_2393113).sum := by decide
  have hdescent : baseEnd_2393113 < baseStart_2393113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393171 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 8]
def baseStart_2393171 : Nat := 118140960795 + 2393171 * 2 ^ 59
def prefixEnd_2393171 : Nat := 4983230072969 + 3 ^ 40 * 2393171 * 2
def baseEnd_2393171 : Nat := 273077113644702542479225

theorem tailTrace_2393171 : CollatzResearch.WordTrace tailWord_2393171 prefixEnd_2393171 273077113644702542479225 := by
  unfold tailWord_2393171
  simp only [CollatzResearch.WordTrace]
  refine ⟨87286117212957662911963367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58190744808638441941308911 87286117212957662911963367)
  ·
    refine ⟨130929175819436494367945051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87286117212957662911963367 130929175819436494367945051)
    ·
      refine ⟨196393763729154741551917577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130929175819436494367945051 196393763729154741551917577)
      ·
        refine ⟨147295322796866056163938183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196393763729154741551917577 147295322796866056163938183)
        ·
          refine ⟨220942984195299084245907275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147295322796866056163938183 220942984195299084245907275)
          ·
            refine ⟨331414476292948626368860913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220942984195299084245907275 331414476292948626368860913)
            ·
              refine ⟨248560857219711469776645685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331414476292948626368860913 248560857219711469776645685)
              ·
                refine ⟨23302580364347950291560533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248560857219711469776645685 23302580364347950291560533)
                ·
                  refine ⟨273077113644702542479225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23302580364347950291560533 273077113644702542479225)
                  ·
                    rfl

theorem cell22_2393171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_2393171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393171 prefixEnd_2393171 := by exact prefixLift 2393171
  have htrace : WordTrace (prefixWord ++ tailWord_2393171) baseStart_2393171 baseEnd_2393171 := by
    simpa [prefixWord, tailWord_2393171, baseEnd_2393171] using wordTrace_append hprefix tailTrace_2393171
  have hstable : (prefixWord ++ tailWord_2393171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393171).length < 2 ^ (prefixWord ++ tailWord_2393171).sum := by decide
  have hdescent : baseEnd_2393171 < baseStart_2393171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393173 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2393173 : Nat := 118140960795 + 2393173 * 2 ^ 59
def prefixEnd_2393173 : Nat := 4983230072969 + 3 ^ 40 * 2393173 * 2
def baseEnd_2393173 : Nat := 819232025574980288887669

theorem tailTrace_2393173 : CollatzResearch.WordTrace tailWord_2393173 prefixEnd_2393173 819232025574980288887669 := by
  unfold tailWord_2393173
  simp only [CollatzResearch.WordTrace]
  refine ⟨87286190158950417253536173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58190793439300278169024115 87286190158950417253536173)
  ·
    refine ⟨32732321309606406470076065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87286190158950417253536173 32732321309606406470076065)
    ·
      refine ⟨24549240982204804852557049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32732321309606406470076065 24549240982204804852557049)
      ·
        refine ⟨18411930736653603639417787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24549240982204804852557049 18411930736653603639417787)
        ·
          refine ⟨27617896104980405459126681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18411930736653603639417787 27617896104980405459126681)
          ·
            refine ⟨20713422078735304094345011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27617896104980405459126681 20713422078735304094345011)
            ·
              refine ⟨31070133118102956141517517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20713422078735304094345011 31070133118102956141517517)
              ·
                refine ⟨11651299919288608553069069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31070133118102956141517517 11651299919288608553069069)
                ·
                  refine ⟨4369237469733228207400901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11651299919288608553069069 4369237469733228207400901)
                  ·
                    refine ⟨819232025574980288887669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369237469733228207400901 819232025574980288887669)
                    ·
                      rfl

theorem cell22_2393173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2393173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393173 prefixEnd_2393173 := by exact prefixLift 2393173
  have htrace : WordTrace (prefixWord ++ tailWord_2393173) baseStart_2393173 baseEnd_2393173 := by
    simpa [prefixWord, tailWord_2393173, baseEnd_2393173] using wordTrace_append hprefix tailTrace_2393173
  have hstable : (prefixWord ++ tailWord_2393173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393173).length < 2 ^ (prefixWord ++ tailWord_2393173).sum := by decide
  have hdescent : baseEnd_2393173 < baseStart_2393173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393181 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2393181 : Nat := 118140960795 + 2393181 * 2 ^ 59
def prefixEnd_2393181 : Nat := 4983230072969 + 3 ^ 40 * 2393181 * 2
def baseEnd_2393181 : Nat := 819234764138470934687645

theorem tailTrace_2393181 : CollatzResearch.WordTrace tailWord_2393181 prefixEnd_2393181 819234764138470934687645 := by
  unfold tailWord_2393181
  simp only [CollatzResearch.WordTrace]
  refine ⟨87286481942921434619827397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58190987961947623079884931 87286481942921434619827397)
  ·
    refine ⟨16366215364297768991217637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87286481942921434619827397 16366215364297768991217637)
    ·
      refine ⟨3068665380805831685853307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16366215364297768991217637 3068665380805831685853307)
      ·
        refine ⟨4602998071208747528779961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068665380805831685853307 4602998071208747528779961)
        ·
          refine ⟨3452248553406560646584971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4602998071208747528779961 3452248553406560646584971)
          ·
            refine ⟨5178372830109840969877457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452248553406560646584971 5178372830109840969877457)
            ·
              refine ⟨3883779622582380727408093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178372830109840969877457 3883779622582380727408093)
              ·
                refine ⟨1456417358468392772778035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3883779622582380727408093 1456417358468392772778035)
                ·
                  refine ⟨2184626037702589159167053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456417358468392772778035 2184626037702589159167053)
                  ·
                    refine ⟨819234764138470934687645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184626037702589159167053 819234764138470934687645)
                    ·
                      rfl

theorem cell22_2393181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2393181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393181 prefixEnd_2393181 := by exact prefixLift 2393181
  have htrace : WordTrace (prefixWord ++ tailWord_2393181) baseStart_2393181 baseEnd_2393181 := by
    simpa [prefixWord, tailWord_2393181, baseEnd_2393181] using wordTrace_append hprefix tailTrace_2393181
  have hstable : (prefixWord ++ tailWord_2393181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393181).length < 2 ^ (prefixWord ++ tailWord_2393181).sum := by decide
  have hdescent : baseEnd_2393181 < baseStart_2393181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393220 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_2393220 : Nat := 118140960795 + 2393220 * 2 ^ 59
def prefixEnd_2393220 : Nat := 4983230072969 + 3 ^ 40 * 2393220 * 2
def baseEnd_2393220 : Nat := 819248114635487832962525

theorem tailTrace_2393220 : CollatzResearch.WordTrace tailWord_2393220 prefixEnd_2393220 819248114635487832962525 := by
  unfold tailWord_2393220
  simp only [CollatzResearch.WordTrace]
  refine ⟨43643952194890072140248557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58191936259853429520331409 43643952194890072140248557)
  ·
    refine ⟨16366482073083777052593209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43643952194890072140248557 16366482073083777052593209)
    ·
      refine ⟨12274861554812832789444907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16366482073083777052593209 12274861554812832789444907)
      ·
        refine ⟨18412292332219249184167361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12274861554812832789444907 18412292332219249184167361)
        ·
          refine ⟨13809219249164436888125521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18412292332219249184167361 13809219249164436888125521)
          ·
            refine ⟨10356914436873327666094141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13809219249164436888125521 10356914436873327666094141)
            ·
              refine ⟨3883842913827497874785303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10356914436873327666094141 3883842913827497874785303)
              ·
                refine ⟨5825764370741246812177955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3883842913827497874785303 5825764370741246812177955)
                ·
                  refine ⟨8738646556111870218266933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5825764370741246812177955 8738646556111870218266933)
                  ·
                    refine ⟨819248114635487832962525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8738646556111870218266933 819248114635487832962525)
                    ·
                      rfl

theorem cell22_2393220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_2393220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393220 prefixEnd_2393220 := by exact prefixLift 2393220
  have htrace : WordTrace (prefixWord ++ tailWord_2393220) baseStart_2393220 baseEnd_2393220 := by
    simpa [prefixWord, tailWord_2393220, baseEnd_2393220] using wordTrace_append hprefix tailTrace_2393220
  have hstable : (prefixWord ++ tailWord_2393220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393220).length < 2 ^ (prefixWord ++ tailWord_2393220).sum := by decide
  have hdescent : baseEnd_2393220 < baseStart_2393220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393342 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2393342 : Nat := 118140960795 + 2393342 * 2 ^ 59
def prefixEnd_2393342 : Nat := 4983230072969 + 3 ^ 40 * 2393342 * 2
def baseEnd_2393342 : Nat := 819289877728720181412151

theorem tailTrace_2393342 : CollatzResearch.WordTrace tailWord_2393342 prefixEnd_2393342 819289877728720181412151 := by
  unfold tailWord_2393342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10911544261917269889554785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58194902730225439410958853 10911544261917269889554785)
  ·
    refine ⟨8183658196437952417166089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10911544261917269889554785 8183658196437952417166089)
    ·
      refine ⟨6137743647328464312874567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8183658196437952417166089 6137743647328464312874567)
      ·
        refine ⟨9206615470992696469311851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6137743647328464312874567 9206615470992696469311851)
        ·
          refine ⟨13809923206489044703967777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9206615470992696469311851 13809923206489044703967777)
          ·
            refine ⟨10357442404866783527975833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13809923206489044703967777 10357442404866783527975833)
            ·
              refine ⟨7768081803650087645981875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10357442404866783527975833 7768081803650087645981875)
              ·
                refine ⟨11652122705475131468972813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7768081803650087645981875 11652122705475131468972813)
                ·
                  refine ⟨4369546014553174300864805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11652122705475131468972813 4369546014553174300864805)
                  ·
                    refine ⟨819289877728720181412151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369546014553174300864805 819289877728720181412151)
                    ·
                      rfl

theorem cell22_2393342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2393342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393342 prefixEnd_2393342 := by exact prefixLift 2393342
  have htrace : WordTrace (prefixWord ++ tailWord_2393342) baseStart_2393342 baseEnd_2393342 := by
    simpa [prefixWord, tailWord_2393342, baseEnd_2393342] using wordTrace_append hprefix tailTrace_2393342
  have hstable : (prefixWord ++ tailWord_2393342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393342).length < 2 ^ (prefixWord ++ tailWord_2393342).sum := by decide
  have hdescent : baseEnd_2393342 < baseStart_2393342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393355 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 1, 5]
def baseStart_2393355 : Nat := 118140960795 + 2393355 * 2 ^ 59
def prefixEnd_2393355 : Nat := 4983230072969 + 3 ^ 40 * 2393355 * 2
def baseEnd_2393355 : Nat := 819294327894392480837111

theorem tailTrace_2393355 : CollatzResearch.WordTrace tailWord_2393355 prefixEnd_2393355 819294327894392480837111 := by
  unfold tailWord_2393355
  simp only [CollatzResearch.WordTrace]
  refine ⟨87292828244291062336661519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58195218829527374891107679 87292828244291062336661519)
  ·
    refine ⟨130939242366436593504992279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87292828244291062336661519 130939242366436593504992279)
    ·
      refine ⟨196408863549654890257488419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130939242366436593504992279 196408863549654890257488419)
      ·
        refine ⟨294613295324482335386232629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196408863549654890257488419 294613295324482335386232629)
        ·
          refine ⟨27619996436670218942459309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 294613295324482335386232629 27619996436670218942459309)
          ·
            refine ⟨10357498663751332103422241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27619996436670218942459309 10357498663751332103422241)
            ·
              refine ⟨7768123997813499077566681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10357498663751332103422241 7768123997813499077566681)
              ·
                refine ⟨5826092998360124308175011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7768123997813499077566681 5826092998360124308175011)
                ·
                  refine ⟨8739139497540186462262517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826092998360124308175011 8739139497540186462262517)
                  ·
                    refine ⟨819294327894392480837111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8739139497540186462262517 819294327894392480837111)
                    ·
                      rfl

theorem cell22_2393355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_2393355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393355 prefixEnd_2393355 := by exact prefixLift 2393355
  have htrace : WordTrace (prefixWord ++ tailWord_2393355) baseStart_2393355 baseEnd_2393355 := by
    simpa [prefixWord, tailWord_2393355, baseEnd_2393355] using wordTrace_append hprefix tailTrace_2393355
  have hstable : (prefixWord ++ tailWord_2393355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393355).length < 2 ^ (prefixWord ++ tailWord_2393355).sum := by decide
  have hdescent : baseEnd_2393355 < baseStart_2393355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393389 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2393389 : Nat := 118140960795 + 2393389 * 2 ^ 59
def prefixEnd_2393389 : Nat := 4983230072969 + 3 ^ 40 * 2393389 * 2
def baseEnd_2393389 : Nat := 819305966789227725487007

theorem tailTrace_2393389 : CollatzResearch.WordTrace tailWord_2393389 prefixEnd_2393389 819305966789227725487007 := by
  unfold tailWord_2393389
  simp only [CollatzResearch.WordTrace]
  refine ⟨87294068326167886143399221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58196045550778590762266147 87294068326167886143399221)
  ·
    refine ⟨8183818905578239325943677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87294068326167886143399221 8183818905578239325943677)
    ·
      refine ⟨3068932089591839747228879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8183818905578239325943677 3068932089591839747228879)
      ·
        refine ⟨4603398134387759620843319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068932089591839747228879 4603398134387759620843319)
        ·
          refine ⟨6905097201581639431264979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603398134387759620843319 6905097201581639431264979)
          ·
            refine ⟨10357645802372459146897469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905097201581639431264979 10357645802372459146897469)
            ·
              refine ⟨3884117175889672180086551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10357645802372459146897469 3884117175889672180086551)
              ·
                refine ⟨5826175763834508270129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884117175889672180086551 5826175763834508270129827)
                ·
                  refine ⟨8739263645751762405194741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826175763834508270129827 8739263645751762405194741)
                  ·
                    refine ⟨819305966789227725487007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8739263645751762405194741 819305966789227725487007)
                    ·
                      rfl

theorem cell22_2393389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2393389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393389 prefixEnd_2393389 := by exact prefixLift 2393389
  have htrace : WordTrace (prefixWord ++ tailWord_2393389) baseStart_2393389 baseEnd_2393389 := by
    simpa [prefixWord, tailWord_2393389, baseEnd_2393389] using wordTrace_append hprefix tailTrace_2393389
  have hstable : (prefixWord ++ tailWord_2393389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393389).length < 2 ^ (prefixWord ++ tailWord_2393389).sum := by decide
  have hdescent : baseEnd_2393389 < baseStart_2393389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393421 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2393421 : Nat := 118140960795 + 2393421 * 2 ^ 59
def prefixEnd_2393421 : Nat := 4983230072969 + 3 ^ 40 * 2393421 * 2
def baseEnd_2393421 : Nat := 819316921043190308686909

theorem tailTrace_2393421 : CollatzResearch.WordTrace tailWord_2393421 prefixEnd_2393421 819316921043190308686909 := by
  unfold tailWord_2393421
  simp only [CollatzResearch.WordTrace]
  refine ⟨87295235462051955608564117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58196823641367970405709411 87295235462051955608564117)
  ·
    refine ⟨4091964162283685419151443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87295235462051955608564117 4091964162283685419151443)
    ·
      refine ⟨6137946243425528128727165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4091964162283685419151443 6137946243425528128727165)
      ·
        refine ⟨2301729841284573048272687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6137946243425528128727165 2301729841284573048272687)
        ·
          refine ⟨3452594761926859572409031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301729841284573048272687 3452594761926859572409031)
          ·
            refine ⟨5178892142890289358613547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452594761926859572409031 5178892142890289358613547)
            ·
              refine ⟨7768338214335434037920321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178892142890289358613547 7768338214335434037920321)
              ·
                refine ⟨5826253660751575528440241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7768338214335434037920321 5826253660751575528440241)
                ·
                  refine ⟨4369690245563681646330181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826253660751575528440241 4369690245563681646330181)
                  ·
                    refine ⟨819316921043190308686909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369690245563681646330181 819316921043190308686909)
                    ·
                      rfl

theorem cell22_2393421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2393421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393421 prefixEnd_2393421 := by exact prefixLift 2393421
  have htrace : WordTrace (prefixWord ++ tailWord_2393421) baseStart_2393421 baseEnd_2393421 := by
    simpa [prefixWord, tailWord_2393421, baseEnd_2393421] using wordTrace_append hprefix tailTrace_2393421
  have hstable : (prefixWord ++ tailWord_2393421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393421).length < 2 ^ (prefixWord ++ tailWord_2393421).sum := by decide
  have hdescent : baseEnd_2393421 < baseStart_2393421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393434 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_2393434 : Nat := 118140960795 + 2393434 * 2 ^ 59
def prefixEnd_2393434 : Nat := 4983230072969 + 3 ^ 40 * 2393434 * 2
def baseEnd_2393434 : Nat := 819321371208862608111869

theorem tailTrace_2393434 : CollatzResearch.WordTrace tailWord_2393434 prefixEnd_2393434 819321371208862608111869 := by
  unfold tailWord_2393434
  simp only [CollatzResearch.WordTrace]
  refine ⟨21823927402751214707196839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58197139740669905885858237 21823927402751214707196839)
  ·
    refine ⟨32735891104126822060795259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21823927402751214707196839 32735891104126822060795259)
    ·
      refine ⟨49103836656190233091192889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32735891104126822060795259 49103836656190233091192889)
      ·
        refine ⟨36827877492142674818394667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49103836656190233091192889 36827877492142674818394667)
        ·
          refine ⟨55241816238214012227592001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36827877492142674818394667 55241816238214012227592001)
          ·
            refine ⟨41431362178660509170694001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55241816238214012227592001 41431362178660509170694001)
            ·
              refine ⟨31073521633995381878020501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41431362178660509170694001 31073521633995381878020501)
              ·
                refine ⟨1456571326593533525532211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31073521633995381878020501 1456571326593533525532211)
                ·
                  refine ⟨2184856989890300288298317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456571326593533525532211 2184856989890300288298317)
                  ·
                    refine ⟨819321371208862608111869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184856989890300288298317 819321371208862608111869)
                    ·
                      rfl

theorem cell22_2393434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_2393434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393434 prefixEnd_2393434 := by exact prefixLift 2393434
  have htrace : WordTrace (prefixWord ++ tailWord_2393434) baseStart_2393434 baseEnd_2393434 := by
    simpa [prefixWord, tailWord_2393434, baseEnd_2393434] using wordTrace_append hprefix tailTrace_2393434
  have hstable : (prefixWord ++ tailWord_2393434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393434).length < 2 ^ (prefixWord ++ tailWord_2393434).sum := by decide
  have hdescent : baseEnd_2393434 < baseStart_2393434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393445 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2393445 : Nat := 118140960795 + 2393445 * 2 ^ 59
def prefixEnd_2393445 : Nat := 4983230072969 + 3 ^ 40 * 2393445 * 2
def baseEnd_2393445 : Nat := 819325136733662246086835

theorem tailTrace_2393445 : CollatzResearch.WordTrace tailWord_2393445 prefixEnd_2393445 819325136733662246086835 := by
  unfold tailWord_2393445
  simp only [CollatzResearch.WordTrace]
  refine ⟨87296110813965007707437789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58197407209310005138291859 87296110813965007707437789)
  ·
    refine ⟨32736041555236877890289171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87296110813965007707437789 32736041555236877890289171)
    ·
      refine ⟨49104062332855316835433757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32736041555236877890289171 49104062332855316835433757)
      ·
        refine ⟨18414023374820743813287659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49104062332855316835433757 18414023374820743813287659)
        ·
          refine ⟨27621035062231115719931489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18414023374820743813287659 27621035062231115719931489)
          ·
            refine ⟨20715776296673336789948617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27621035062231115719931489 20715776296673336789948617)
            ·
              refine ⟨15536832222505002592461463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20715776296673336789948617 15536832222505002592461463)
              ·
                refine ⟨23305248333757503888692195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15536832222505002592461463 23305248333757503888692195)
                ·
                  refine ⟨34957872500636255833038293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23305248333757503888692195 34957872500636255833038293)
                  ·
                    refine ⟨819325136733662246086835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34957872500636255833038293 819325136733662246086835)
                    ·
                      rfl

theorem cell22_2393445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2393445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393445 prefixEnd_2393445 := by exact prefixLift 2393445
  have htrace : WordTrace (prefixWord ++ tailWord_2393445) baseStart_2393445 baseEnd_2393445 := by
    simpa [prefixWord, tailWord_2393445, baseEnd_2393445] using wordTrace_append hprefix tailTrace_2393445
  have hstable : (prefixWord ++ tailWord_2393445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393445).length < 2 ^ (prefixWord ++ tailWord_2393445).sum := by decide
  have hdescent : baseEnd_2393445 < baseStart_2393445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393477 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_2393477 : Nat := 118140960795 + 2393477 * 2 ^ 59
def prefixEnd_2393477 : Nat := 4983230072969 + 3 ^ 40 * 2393477 * 2
def baseEnd_2393477 : Nat := 819336090987624829286737

theorem tailTrace_2393477 : CollatzResearch.WordTrace tailWord_2393477 prefixEnd_2393477 819336090987624829286737 := by
  unfold tailWord_2393477
  simp only [CollatzResearch.WordTrace]
  refine ⟨87297277949849077172602685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58198185299899384781735123 87297277949849077172602685)
  ·
    refine ⟨32736479231193403939726007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87297277949849077172602685 32736479231193403939726007)
    ·
      refine ⟨49104718846790105909589011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32736479231193403939726007 49104718846790105909589011)
      ·
        refine ⟨73657078270185158864383517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49104718846790105909589011 73657078270185158864383517)
        ·
          refine ⟨27621404351319434574143819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73657078270185158864383517 27621404351319434574143819)
          ·
            refine ⟨41432106526979151861215729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27621404351319434574143819 41432106526979151861215729)
            ·
              refine ⟨31074079895234363895911797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41432106526979151861215729 31074079895234363895911797)
              ·
                refine ⟨2913194990178221615241731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31074079895234363895911797 2913194990178221615241731)
                ·
                  refine ⟨4369792485267332422862597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913194990178221615241731 4369792485267332422862597)
                  ·
                    refine ⟨819336090987624829286737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369792485267332422862597 819336090987624829286737)
                    ·
                      rfl

theorem cell22_2393477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_2393477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393477 prefixEnd_2393477 := by exact prefixLift 2393477
  have htrace : WordTrace (prefixWord ++ tailWord_2393477) baseStart_2393477 baseEnd_2393477 := by
    simpa [prefixWord, tailWord_2393477, baseEnd_2393477] using wordTrace_append hprefix tailTrace_2393477
  have hstable : (prefixWord ++ tailWord_2393477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393477).length < 2 ^ (prefixWord ++ tailWord_2393477).sum := by decide
  have hdescent : baseEnd_2393477 < baseStart_2393477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393507 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 1, 5]
def baseStart_2393507 : Nat := 118140960795 + 2393507 * 2 ^ 59
def prefixEnd_2393507 : Nat := 4983230072969 + 3 ^ 40 * 2393507 * 2
def baseEnd_2393507 : Nat := 819346360600714751036645

theorem tailTrace_2393507 : CollatzResearch.WordTrace tailWord_2393507 prefixEnd_2393507 819346360600714751036645 := by
  unfold tailWord_2393507
  simp only [CollatzResearch.WordTrace]
  refine ⟨87298372139740392296194775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58198914759826928197463183 87298372139740392296194775)
  ·
    refine ⟨130947558209610588444292163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87298372139740392296194775 130947558209610588444292163)
    ·
      refine ⟨196421337314415882666438245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130947558209610588444292163 196421337314415882666438245)
      ·
        refine ⟨36829000746452977999957171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196421337314415882666438245 36829000746452977999957171)
        ·
          refine ⟨55243501119679466999935757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36829000746452977999957171 55243501119679466999935757)
          ·
            refine ⟨20716312919879800124975909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55243501119679466999935757 20716312919879800124975909)
            ·
              refine ⟨3884308672477462523432983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20716312919879800124975909 3884308672477462523432983)
              ·
                refine ⟨5826463008716193785149475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884308672477462523432983 5826463008716193785149475)
                ·
                  refine ⟨8739694513074290677724213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826463008716193785149475 8739694513074290677724213)
                  ·
                    refine ⟨819346360600714751036645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8739694513074290677724213 819346360600714751036645)
                    ·
                      rfl

theorem cell22_2393507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].length) (baseStart_2393507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393507 prefixEnd_2393507 := by exact prefixLift 2393507
  have htrace : WordTrace (prefixWord ++ tailWord_2393507) baseStart_2393507 baseEnd_2393507 := by
    simpa [prefixWord, tailWord_2393507, baseEnd_2393507] using wordTrace_append hprefix tailTrace_2393507
  have hstable : (prefixWord ++ tailWord_2393507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393507).length < 2 ^ (prefixWord ++ tailWord_2393507).sum := by decide
  have hdescent : baseEnd_2393507 < baseStart_2393507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393522 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_2393522 : Nat := 118140960795 + 2393522 * 2 ^ 59
def prefixEnd_2393522 : Nat := 4983230072969 + 3 ^ 40 * 2393522 * 2
def baseEnd_2393522 : Nat := 819351495407259711911599

theorem tailTrace_2393522 : CollatzResearch.WordTrace tailWord_2393522 prefixEnd_2393522 819351495407259711911599 := by
  unfold tailWord_2393522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21824729808671512464497705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58199279489790699905327213 21824729808671512464497705)
  ·
    refine ⟨16368547356503634348373279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21824729808671512464497705 16368547356503634348373279)
    ·
      refine ⟨24552821034755451522559919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16368547356503634348373279 24552821034755451522559919)
      ·
        refine ⟨36829231552133177283839879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24552821034755451522559919 36829231552133177283839879)
        ·
          refine ⟨55243847328199765925759819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36829231552133177283839879 55243847328199765925759819)
          ·
            refine ⟨82865770992299648888639729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55243847328199765925759819 82865770992299648888639729)
            ·
              refine ⟨62149328244224736666479797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82865770992299648888639729 62149328244224736666479797)
              ·
                refine ⟨5826499522896069062482481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62149328244224736666479797 5826499522896069062482481)
                ·
                  refine ⟨4369874642172051796861861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826499522896069062482481 4369874642172051796861861)
                  ·
                    refine ⟨819351495407259711911599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369874642172051796861861 819351495407259711911599)
                    ·
                      rfl

theorem cell22_2393522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_2393522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393522 prefixEnd_2393522 := by exact prefixLift 2393522
  have htrace : WordTrace (prefixWord ++ tailWord_2393522) baseStart_2393522 baseEnd_2393522 := by
    simpa [prefixWord, tailWord_2393522, baseEnd_2393522] using wordTrace_append hprefix tailTrace_2393522
  have hstable : (prefixWord ++ tailWord_2393522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393522).length < 2 ^ (prefixWord ++ tailWord_2393522).sum := by decide
  have hdescent : baseEnd_2393522 < baseStart_2393522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393535 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_2393535 : Nat := 118140960795 + 2393535 * 2 ^ 59
def prefixEnd_2393535 : Nat := 4983230072969 + 3 ^ 40 * 2393535 * 2
def baseEnd_2393535 : Nat := 819355945572932011336559

theorem tailTrace_2393535 : CollatzResearch.WordTrace tailWord_2393535 prefixEnd_2393535 819355945572932011336559 := by
  unfold tailWord_2393535
  simp only [CollatzResearch.WordTrace]
  refine ⟨87299393383638953078214059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58199595589092635385476039 87299393383638953078214059)
  ·
    refine ⟨130949090075458429617321089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87299393383638953078214059 130949090075458429617321089)
    ·
      refine ⟨98211817556593822212990817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130949090075458429617321089 98211817556593822212990817)
      ·
        refine ⟨73658863167445366659743113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98211817556593822212990817 73658863167445366659743113)
        ·
          refine ⟨55244147375584024994807335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73658863167445366659743113 55244147375584024994807335)
          ·
            refine ⟨82866221063376037492211003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55244147375584024994807335 82866221063376037492211003)
            ·
              refine ⟨124299331595064056238316505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82866221063376037492211003 124299331595064056238316505)
              ·
                refine ⟨93224498696298042178737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124299331595064056238316505 93224498696298042178737379)
                ·
                  refine ⟨139836748044447063268106069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93224498696298042178737379 139836748044447063268106069)
                  ·
                    refine ⟨819355945572932011336559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 139836748044447063268106069 819355945572932011336559)
                    ·
                      rfl

theorem cell22_2393535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_2393535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393535 prefixEnd_2393535 := by exact prefixLift 2393535
  have htrace : WordTrace (prefixWord ++ tailWord_2393535) baseStart_2393535 baseEnd_2393535 := by
    simpa [prefixWord, tailWord_2393535, baseEnd_2393535] using wordTrace_append hprefix tailTrace_2393535
  have hstable : (prefixWord ++ tailWord_2393535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393535).length < 2 ^ (prefixWord ++ tailWord_2393535).sum := by decide
  have hdescent : baseEnd_2393535 < baseStart_2393535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393552 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_2393552 : Nat := 118140960795 + 2393552 * 2 ^ 59
def prefixEnd_2393552 : Nat := 4983230072969 + 3 ^ 40 * 2393552 * 2
def baseEnd_2393552 : Nat := 819361765020349633661507

theorem tailTrace_2393552 : CollatzResearch.WordTrace tailWord_2393552 prefixEnd_2393552 819361765020349633661507 := by
  unfold tailWord_2393552
  simp only [CollatzResearch.WordTrace]
  refine ⟨43650006712288682490791455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58200008949718243321055273 43650006712288682490791455)
  ·
    refine ⟨65475010068433023736187183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43650006712288682490791455 65475010068433023736187183)
    ·
      refine ⟨98212515102649535604280775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65475010068433023736187183 98212515102649535604280775)
      ·
        refine ⟨147318772653974303406421163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98212515102649535604280775 147318772653974303406421163)
        ·
          refine ⟨220978158980961455109631745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147318772653974303406421163 220978158980961455109631745)
          ·
            refine ⟨165733619235721091332223809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220978158980961455109631745 165733619235721091332223809)
            ·
              refine ⟨124300214426790818499167857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165733619235721091332223809 124300214426790818499167857)
              ·
                refine ⟨93225160820093113874375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124300214426790818499167857 93225160820093113874375893)
                ·
                  refine ⟨2184964706720932356430685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93225160820093113874375893 2184964706720932356430685)
                  ·
                    refine ⟨819361765020349633661507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184964706720932356430685 819361765020349633661507)
                    ·
                      rfl

theorem cell22_2393552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_2393552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393552 prefixEnd_2393552 := by exact prefixLift 2393552
  have htrace : WordTrace (prefixWord ++ tailWord_2393552) baseStart_2393552 baseEnd_2393552 := by
    simpa [prefixWord, tailWord_2393552, baseEnd_2393552] using wordTrace_append hprefix tailTrace_2393552
  have hstable : (prefixWord ++ tailWord_2393552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393552).length < 2 ^ (prefixWord ++ tailWord_2393552).sum := by decide
  have hdescent : baseEnd_2393552 < baseStart_2393552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393569 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_2393569 : Nat := 118140960795 + 2393569 * 2 ^ 59
def prefixEnd_2393569 : Nat := 4983230072969 + 3 ^ 40 * 2393569 * 2
def baseEnd_2393569 : Nat := 819367584467767255986455

theorem tailTrace_2393569 : CollatzResearch.WordTrace tailWord_2393569 prefixEnd_2393569 819367584467767255986455 := by
  unfold tailWord_2393569
  simp only [CollatzResearch.WordTrace]
  refine ⟨87300633465515776884951761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58200422310343851256634507 87300633465515776884951761)
  ·
    refine ⟨65475475099136832663713821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87300633465515776884951761 65475475099136832663713821)
    ·
      refine ⟨24553303162176312248892683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65475475099136832663713821 24553303162176312248892683)
      ·
        refine ⟨36829954743264468373339025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24553303162176312248892683 36829954743264468373339025)
        ·
          refine ⟨27622466057448351280004269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36829954743264468373339025 27622466057448351280004269)
          ·
            refine ⟨10358424771543131730001601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27622466057448351280004269 10358424771543131730001601)
            ·
              refine ⟨7768818578657348797501201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10358424771543131730001601 7768818578657348797501201)
              ·
                refine ⟨5826613933993011598125901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7768818578657348797501201 5826613933993011598125901)
                ·
                  refine ⟨2184980225247379349297213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5826613933993011598125901 2184980225247379349297213)
                  ·
                    refine ⟨819367584467767255986455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184980225247379349297213 819367584467767255986455)
                    ·
                      rfl

theorem cell22_2393569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_2393569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393569 prefixEnd_2393569 := by exact prefixLift 2393569
  have htrace : WordTrace (prefixWord ++ tailWord_2393569) baseStart_2393569 baseEnd_2393569 := by
    simpa [prefixWord, tailWord_2393569, baseEnd_2393569] using wordTrace_append hprefix tailTrace_2393569
  have hstable : (prefixWord ++ tailWord_2393569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393569).length < 2 ^ (prefixWord ++ tailWord_2393569).sum := by decide
  have hdescent : baseEnd_2393569 < baseStart_2393569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393582 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_2393582 : Nat := 118140960795 + 2393582 * 2 ^ 59
def prefixEnd_2393582 : Nat := 4983230072969 + 3 ^ 40 * 2393582 * 2
def baseEnd_2393582 : Nat := 273124011544479851803805

theorem tailTrace_2393582 : CollatzResearch.WordTrace tailWord_2393582 prefixEnd_2393582 273124011544479851803805 := by
  unfold tailWord_2393582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912638451808585013146875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58200738409645786736783333 10912638451808585013146875)
  ·
    refine ⟨16368957677712877519720313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10912638451808585013146875 16368957677712877519720313)
    ·
      refine ⟨12276718258284658139790235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16368957677712877519720313 12276718258284658139790235)
      ·
        refine ⟨18415077387426987209685353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12276718258284658139790235 18415077387426987209685353)
        ·
          refine ⟨13811308040570240407264015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18415077387426987209685353 13811308040570240407264015)
          ·
            refine ⟨20716962060855360610896023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13811308040570240407264015 20716962060855360610896023)
            ·
              refine ⟨31075443091283040916344035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20716962060855360610896023 31075443091283040916344035)
              ·
                refine ⟨46613164636924561374516053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31075443091283040916344035 46613164636924561374516053)
                ·
                  refine ⟨273124011544479851803805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46613164636924561374516053 273124011544479851803805)
                  ·
                    rfl

theorem cell22_2393582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_2393582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393582 prefixEnd_2393582 := by exact prefixLift 2393582
  have htrace : WordTrace (prefixWord ++ tailWord_2393582) baseStart_2393582 baseEnd_2393582 := by
    simpa [prefixWord, tailWord_2393582, baseEnd_2393582] using wordTrace_append hprefix tailTrace_2393582
  have hstable : (prefixWord ++ tailWord_2393582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393582).length < 2 ^ (prefixWord ++ tailWord_2393582).sum := by decide
  have hdescent : baseEnd_2393582 < baseStart_2393582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393629 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2393629 : Nat := 118140960795 + 2393629 * 2 ^ 59
def prefixEnd_2393629 : Nat := 4983230072969 + 3 ^ 40 * 2393629 * 2
def baseEnd_2393629 : Nat := 819388123693947099486271

theorem tailTrace_2393629 : CollatzResearch.WordTrace tailWord_2393629 prefixEnd_2393629 819388123693947099486271 := by
  unfold tailWord_2393629
  simp only [CollatzResearch.WordTrace]
  refine ⟨87302821845298407132135941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58201881230198938088090627 87302821845298407132135941)
  ·
    refine ⟨16369279095993451337275489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87302821845298407132135941 16369279095993451337275489)
    ·
      refine ⟨12276959321995088502956617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16369279095993451337275489 12276959321995088502956617)
      ·
        refine ⟨9207719491496316377217463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12276959321995088502956617 9207719491496316377217463)
        ·
          refine ⟨13811579237244474565826195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9207719491496316377217463 13811579237244474565826195)
          ·
            refine ⟨20717368855866711848739293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13811579237244474565826195 20717368855866711848739293)
            ·
              refine ⟨7769013320950016943277235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20717368855866711848739293 7769013320950016943277235)
              ·
                refine ⟨11653519981425025414915853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7769013320950016943277235 11653519981425025414915853)
                ·
                  refine ⟨4370069993034384530593445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11653519981425025414915853 4370069993034384530593445)
                  ·
                    refine ⟨819388123693947099486271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4370069993034384530593445 819388123693947099486271)
                    ·
                      rfl

theorem cell22_2393629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2393629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393629 prefixEnd_2393629 := by exact prefixLift 2393629
  have htrace : WordTrace (prefixWord ++ tailWord_2393629) baseStart_2393629 baseEnd_2393629 := by
    simpa [prefixWord, tailWord_2393629, baseEnd_2393629] using wordTrace_append hprefix tailTrace_2393629
  have hstable : (prefixWord ++ tailWord_2393629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393629).length < 2 ^ (prefixWord ++ tailWord_2393629).sum := by decide
  have hdescent : baseEnd_2393629 < baseStart_2393629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393654 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2393654 : Nat := 118140960795 + 2393654 * 2 ^ 59
def prefixEnd_2393654 : Nat := 4983230072969 + 3 ^ 40 * 2393654 * 2
def baseEnd_2393654 : Nat := 819396681704855367611195

theorem tailTrace_2393654 : CollatzResearch.WordTrace tailWord_2393654 prefixEnd_2393654 819396681704855367611195 := by
  unfold tailWord_2393654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456483354387989775112251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58202489113471890934530677 5456483354387989775112251)
  ·
    refine ⟨8184725031581984662668377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456483354387989775112251 8184725031581984662668377)
    ·
      refine ⟨6138543773686488497001283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8184725031581984662668377 6138543773686488497001283)
      ·
        refine ⟨9207815660529732745501925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6138543773686488497001283 9207815660529732745501925)
        ·
          refine ⟨1726465436349324889781611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9207815660529732745501925 1726465436349324889781611)
          ·
            refine ⟨2589698154523987334672417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726465436349324889781611 2589698154523987334672417)
            ·
              refine ⟨1942273615892990501004313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2589698154523987334672417 1942273615892990501004313)
              ·
                refine ⟨1456705211919742875753235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942273615892990501004313 1456705211919742875753235)
                ·
                  refine ⟨2185057817879614313629853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456705211919742875753235 2185057817879614313629853)
                  ·
                    refine ⟨819396681704855367611195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185057817879614313629853 819396681704855367611195)
                    ·
                      rfl

theorem cell22_2393654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2393654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393654 prefixEnd_2393654 := by exact prefixLift 2393654
  have htrace : WordTrace (prefixWord ++ tailWord_2393654) baseStart_2393654 baseEnd_2393654 := by
    simpa [prefixWord, tailWord_2393654, baseEnd_2393654] using wordTrace_append hprefix tailTrace_2393654
  have hstable : (prefixWord ++ tailWord_2393654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393654).length < 2 ^ (prefixWord ++ tailWord_2393654).sum := by decide
  have hdescent : baseEnd_2393654 < baseStart_2393654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393676 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_2393676 : Nat := 118140960795 + 2393676 * 2 ^ 59
def prefixEnd_2393676 : Nat := 4983230072969 + 3 ^ 40 * 2393676 * 2
def baseEnd_2393676 : Nat := 819404212754454643561127

theorem tailTrace_2393676 : CollatzResearch.WordTrace tailWord_2393676 prefixEnd_2393676 819404212754454643561127 := by
  unfold tailWord_2393676
  simp only [CollatzResearch.WordTrace]
  refine ⟨43652268038064067079548441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58203024050752089439397921 43652268038064067079548441)
  ·
    refine ⟨32739201028548050309661331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43652268038064067079548441 32739201028548050309661331)
    ·
      refine ⟨49108801542822075464491997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32739201028548050309661331 49108801542822075464491997)
      ·
        refine ⟨18415800578558278299184499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49108801542822075464491997 18415800578558278299184499)
        ·
          refine ⟨27623700867837417448776749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18415800578558278299184499 27623700867837417448776749)
          ·
            refine ⟨10358887825439031543291281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27623700867837417448776749 10358887825439031543291281)
            ·
              refine ⟨7769165869079273657468461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10358887825439031543291281 7769165869079273657468461)
              ·
                refine ⟨2913437200904727621550673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7769165869079273657468461 2913437200904727621550673)
                ·
                  refine ⟨2185077900678545716163005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913437200904727621550673 2185077900678545716163005)
                  ·
                    refine ⟨819404212754454643561127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185077900678545716163005 819404212754454643561127)
                    ·
                      rfl

theorem cell22_2393676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_2393676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393676 prefixEnd_2393676 := by exact prefixLift 2393676
  have htrace : WordTrace (prefixWord ++ tailWord_2393676) baseStart_2393676 baseEnd_2393676 := by
    simpa [prefixWord, tailWord_2393676, baseEnd_2393676] using wordTrace_append hprefix tailTrace_2393676
  have hstable : (prefixWord ++ tailWord_2393676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393676).length < 2 ^ (prefixWord ++ tailWord_2393676).sum := by decide
  have hdescent : baseEnd_2393676 < baseStart_2393676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393710 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2393710 : Nat := 118140960795 + 2393710 * 2 ^ 59
def prefixEnd_2393710 : Nat := 4983230072969 + 3 ^ 40 * 2393710 * 2
def baseEnd_2393710 : Nat := 819415851649289888211023

theorem tailTrace_2393710 : CollatzResearch.WordTrace tailWord_2393710 prefixEnd_2393710 819415851649289888211023 := by
  unfold tailWord_2393710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913222019750619745729323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58203850772003305310556389 10913222019750619745729323)
  ·
    refine ⟨16369833029625929618593985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10913222019750619745729323 16369833029625929618593985)
    ·
      refine ⟨12277374772219447213945489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16369833029625929618593985 12277374772219447213945489)
      ·
        refine ⟨9208031079164585410459117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12277374772219447213945489 9208031079164585410459117)
        ·
          refine ⟨3453011654686719528922169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9208031079164585410459117 3453011654686719528922169)
          ·
            refine ⟨2589758741015039646691627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453011654686719528922169 2589758741015039646691627)
            ·
              refine ⟨3884638111522559470037441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589758741015039646691627 3884638111522559470037441)
              ·
                refine ⟨2913478583641919602528081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884638111522559470037441 2913478583641919602528081)
                ·
                  refine ⟨2185108937731439701896061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913478583641919602528081 2185108937731439701896061)
                  ·
                    refine ⟨819415851649289888211023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185108937731439701896061 819415851649289888211023)
                    ·
                      rfl

theorem cell22_2393710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2393710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393710 prefixEnd_2393710 := by exact prefixLift 2393710
  have htrace : WordTrace (prefixWord ++ tailWord_2393710) baseStart_2393710 baseEnd_2393710 := by
    simpa [prefixWord, tailWord_2393710, baseEnd_2393710] using wordTrace_append hprefix tailTrace_2393710
  have hstable : (prefixWord ++ tailWord_2393710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393710).length < 2 ^ (prefixWord ++ tailWord_2393710).sum := by decide
  have hdescent : baseEnd_2393710 < baseStart_2393710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393721 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_2393721 : Nat := 118140960795 + 2393721 * 2 ^ 59
def prefixEnd_2393721 : Nat := 4983230072969 + 3 ^ 40 * 2393721 * 2
def baseEnd_2393721 : Nat := 819419617174089526185989

theorem tailTrace_2393721 : CollatzResearch.WordTrace tailWord_2393721 prefixEnd_2393721 819419617174089526185989 := by
  unfold tailWord_2393721
  simp only [CollatzResearch.WordTrace]
  refine ⟨87306177360965106844485017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58204118240643404562990011 87306177360965106844485017)
  ·
    refine ⟨65479633020723830133363763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87306177360965106844485017 65479633020723830133363763)
    ·
      refine ⟨98219449531085745200045645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65479633020723830133363763 98219449531085745200045645)
      ·
        refine ⟨36832293574157154450017117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98219449531085745200045645 36832293574157154450017117)
        ·
          refine ⟨13812110090308932918756419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36832293574157154450017117 13812110090308932918756419)
          ·
            refine ⟨20718165135463399378134629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13812110090308932918756419 20718165135463399378134629)
            ·
              refine ⟨3884655962899387383400243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20718165135463399378134629 3884655962899387383400243)
              ·
                refine ⟨5826983944349081075100365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884655962899387383400243 5826983944349081075100365)
                ·
                  refine ⟨2185118979130905403162637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5826983944349081075100365 2185118979130905403162637)
                  ·
                    refine ⟨819419617174089526185989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185118979130905403162637 819419617174089526185989)
                    ·
                      rfl

theorem cell22_2393721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_2393721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393721 prefixEnd_2393721 := by exact prefixLift 2393721
  have htrace : WordTrace (prefixWord ++ tailWord_2393721) baseStart_2393721 baseEnd_2393721 := by
    simpa [prefixWord, tailWord_2393721, baseEnd_2393721] using wordTrace_append hprefix tailTrace_2393721
  have hstable : (prefixWord ++ tailWord_2393721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393721).length < 2 ^ (prefixWord ++ tailWord_2393721).sum := by decide
  have hdescent : baseEnd_2393721 < baseStart_2393721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393828 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_2393828 : Nat := 118140960795 + 2393828 * 2 ^ 59
def prefixEnd_2393828 : Nat := 4983230072969 + 3 ^ 40 * 2393828 * 2
def baseEnd_2393828 : Nat := 819456245460776913760661

theorem tailTrace_2393828 : CollatzResearch.WordTrace tailWord_2393828 prefixEnd_2393828 819456245460776913760661 := by
  unfold tailWord_2393828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43655039985788732059315069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58206719981051642745753425 43655039985788732059315069)
  ·
    refine ⟨16370639994670774522243151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43655039985788732059315069 16370639994670774522243151)
    ·
      refine ⟨24555959992006161783364727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16370639994670774522243151 24555959992006161783364727)
      ·
        refine ⟨36833939988009242675047091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24555959992006161783364727 36833939988009242675047091)
        ·
          refine ⟨55250909982013864012570637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36833939988009242675047091 55250909982013864012570637)
          ·
            refine ⟨20719091243255199004713989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55250909982013864012570637 20719091243255199004713989)
            ·
              refine ⟨3884829608110349813383873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20719091243255199004713989 3884829608110349813383873)
              ·
                refine ⟨2913622206082762360037905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884829608110349813383873 2913622206082762360037905)
                ·
                  refine ⟨2185216654562071770028429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913622206082762360037905 2185216654562071770028429)
                  ·
                    refine ⟨819456245460776913760661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185216654562071770028429 819456245460776913760661)
                    ·
                      rfl

theorem cell22_2393828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_2393828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393828 prefixEnd_2393828 := by exact prefixLift 2393828
  have htrace : WordTrace (prefixWord ++ tailWord_2393828) baseStart_2393828 baseEnd_2393828 := by
    simpa [prefixWord, tailWord_2393828, baseEnd_2393828] using wordTrace_append hprefix tailTrace_2393828
  have hstable : (prefixWord ++ tailWord_2393828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393828).length < 2 ^ (prefixWord ++ tailWord_2393828).sum := by decide
  have hdescent : baseEnd_2393828 < baseStart_2393828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393841 : List Nat := [1, 2, 2, 2, 2, 5, 1, 7]
def baseStart_2393841 : Nat := 118140960795 + 2393841 * 2 ^ 59
def prefixEnd_2393841 : Nat := 4983230072969 + 3 ^ 40 * 2393841 * 2
def baseEnd_2393841 : Nat := 91051188402938801465069

theorem tailTrace_2393841 : CollatzResearch.WordTrace tailWord_2393841 prefixEnd_2393841 91051188402938801465069 := by
  unfold tailWord_2393841
  simp only [CollatzResearch.WordTrace]
  refine ⟨87310554120530367338853377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58207036080353578225902251 87310554120530367338853377)
  ·
    refine ⟨65482915590397775504140033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87310554120530367338853377 65482915590397775504140033)
    ·
      refine ⟨49112186692798331628105025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65482915590397775504140033 49112186692798331628105025)
      ·
        refine ⟨36834140019598748721078769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49112186692798331628105025 36834140019598748721078769)
        ·
          refine ⟨27625605014699061540809077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36834140019598748721078769 27625605014699061540809077)
          ·
            refine ⟨2589900470128037019450851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27625605014699061540809077 2589900470128037019450851)
            ·
              refine ⟨3884850705192055529176277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589900470128037019450851 3884850705192055529176277)
              ·
                refine ⟨91051188402938801465069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3884850705192055529176277 91051188402938801465069)
                ·
                  rfl

theorem cell22_2393841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 7].length) (baseStart_2393841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393841 prefixEnd_2393841 := by exact prefixLift 2393841
  have htrace : WordTrace (prefixWord ++ tailWord_2393841) baseStart_2393841 baseEnd_2393841 := by
    simpa [prefixWord, tailWord_2393841, baseEnd_2393841] using wordTrace_append hprefix tailTrace_2393841
  have hstable : (prefixWord ++ tailWord_2393841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393841).length < 2 ^ (prefixWord ++ tailWord_2393841).sum := by decide
  have hdescent : baseEnd_2393841 < baseStart_2393841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393856 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_2393856 : Nat := 118140960795 + 2393856 * 2 ^ 59
def prefixEnd_2393856 : Nat := 4983230072969 + 3 ^ 40 * 2393856 * 2
def baseEnd_2393856 : Nat := 819465830432994174060575

theorem tailTrace_2393856 : CollatzResearch.WordTrace tailWord_2393856 prefixEnd_2393856 819465830432994174060575 := by
  unfold tailWord_2393856
  simp only [CollatzResearch.WordTrace]
  refine ⟨43655550607738012450324711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58207400810317349933766281 43655550607738012450324711)
  ·
    refine ⟨65483325911607018675487067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43655550607738012450324711 65483325911607018675487067)
    ·
      refine ⟨98224988867410528013230601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65483325911607018675487067 98224988867410528013230601)
      ·
        refine ⟨73668741650557896009922951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98224988867410528013230601 73668741650557896009922951)
        ·
          refine ⟨110503112475836844014884427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73668741650557896009922951 110503112475836844014884427)
          ·
            refine ⟨165754668713755266022326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110503112475836844014884427 165754668713755266022326641)
            ·
              refine ⟨124316001535316449516744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165754668713755266022326641 124316001535316449516744981)
              ·
                refine ⟨5827312571967958571097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124316001535316449516744981 5827312571967958571097421)
                ·
                  refine ⟨2185242214487984464161533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5827312571967958571097421 2185242214487984464161533)
                  ·
                    refine ⟨819465830432994174060575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185242214487984464161533 819465830432994174060575)
                    ·
                      rfl

theorem cell22_2393856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_2393856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393856 prefixEnd_2393856 := by exact prefixLift 2393856
  have htrace : WordTrace (prefixWord ++ tailWord_2393856) baseStart_2393856 baseEnd_2393856 := by
    simpa [prefixWord, tailWord_2393856, baseEnd_2393856] using wordTrace_append hprefix tailTrace_2393856
  have hstable : (prefixWord ++ tailWord_2393856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393856).length < 2 ^ (prefixWord ++ tailWord_2393856).sum := by decide
  have hdescent : baseEnd_2393856 < baseStart_2393856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393858 : List Nat := [3, 4, 1, 1, 1, 1, 5, 6]
def baseStart_2393858 : Nat := 118140960795 + 2393858 * 2 ^ 59
def prefixEnd_2393858 : Nat := 4983230072969 + 3 ^ 40 * 2393858 * 2
def baseEnd_2393858 : Nat := 91051835008207426167841

theorem tailTrace_2393858 : CollatzResearch.WordTrace tailWord_2393858 prefixEnd_2393858 91051835008207426167841 := by
  unfold tailWord_2393858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21827793540367194810555557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58207449440979186161481485 21827793540367194810555557)
  ·
    refine ⟨4092711288818849026979167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21827793540367194810555557 4092711288818849026979167)
    ·
      refine ⟨6139066933228273540468751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092711288818849026979167 6139066933228273540468751)
      ·
        refine ⟨9208600399842410310703127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139066933228273540468751 9208600399842410310703127)
        ·
          refine ⟨13812900599763615466054691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9208600399842410310703127 13812900599763615466054691)
          ·
            refine ⟨20719350899645423199082037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13812900599763615466054691 20719350899645423199082037)
            ·
              refine ⟨1942439146841758424913941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20719350899645423199082037 1942439146841758424913941)
              ·
                refine ⟨91051835008207426167841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1942439146841758424913941 91051835008207426167841)
                ·
                  rfl

theorem cell22_2393858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_2393858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393858 prefixEnd_2393858 := by exact prefixLift 2393858
  have htrace : WordTrace (prefixWord ++ tailWord_2393858) baseStart_2393858 baseEnd_2393858 := by
    simpa [prefixWord, tailWord_2393858, baseEnd_2393858] using wordTrace_append hprefix tailTrace_2393858
  have hstable : (prefixWord ++ tailWord_2393858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393858).length < 2 ^ (prefixWord ++ tailWord_2393858).sum := by decide
  have hdescent : baseEnd_2393858 < baseStart_2393858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393890 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2393890 : Nat := 118140960795 + 2393890 * 2 ^ 59
def prefixEnd_2393890 : Nat := 4983230072969 + 3 ^ 40 * 2393890 * 2
def baseEnd_2393890 : Nat := 819477469327829418710471

theorem tailTrace_2393890 : CollatzResearch.WordTrace tailWord_2393890 prefixEnd_2393890 819477469327829418710471 := by
  unfold tailWord_2393890
  simp only [CollatzResearch.WordTrace]
  refine ⟨21828085324338212176846781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58208227531568565804924749 21828085324338212176846781)
  ·
    refine ⟨8185531996626829566317543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21828085324338212176846781 8185531996626829566317543)
    ·
      refine ⟨12278297994940244349476315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8185531996626829566317543 12278297994940244349476315)
      ·
        refine ⟨18417446992410366524214473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12278297994940244349476315 18417446992410366524214473)
        ·
          refine ⟨13813085244307774893160855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18417446992410366524214473 13813085244307774893160855)
          ·
            refine ⟨20719627866461662339741283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13813085244307774893160855 20719627866461662339741283)
            ·
              refine ⟨31079441799692493509611925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20719627866461662339741283 31079441799692493509611925)
              ·
                refine ⟨1456848834360585633263059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31079441799692493509611925 1456848834360585633263059)
                ·
                  refine ⟨2185273251540878449894589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456848834360585633263059 2185273251540878449894589)
                  ·
                    refine ⟨819477469327829418710471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185273251540878449894589 819477469327829418710471)
                    ·
                      rfl

theorem cell22_2393890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2393890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393890 prefixEnd_2393890 := by exact prefixLift 2393890
  have htrace : WordTrace (prefixWord ++ tailWord_2393890) baseStart_2393890 baseEnd_2393890 := by
    simpa [prefixWord, tailWord_2393890, baseEnd_2393890] using wordTrace_append hprefix tailTrace_2393890
  have hstable : (prefixWord ++ tailWord_2393890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393890).length < 2 ^ (prefixWord ++ tailWord_2393890).sum := by decide
  have hdescent : baseEnd_2393890 < baseStart_2393890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393916 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2393916 : Nat := 118140960795 + 2393916 * 2 ^ 59
def prefixEnd_2393916 : Nat := 4983230072969 + 3 ^ 40 * 2393916 * 2
def baseEnd_2393916 : Nat := 819486369659174017560391

theorem tailTrace_2393916 : CollatzResearch.WordTrace tailWord_2393916 prefixEnd_2393916 819486369659174017560391 := by
  unfold tailWord_2393916
  simp only [CollatzResearch.WordTrace]
  refine ⟨43656644797629327573916801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58208859730172436765222401 43656644797629327573916801)
  ·
    refine ⟨32742483598221995680437601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43656644797629327573916801 32742483598221995680437601)
    ·
      refine ⟨24556862698666496760328201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32742483598221995680437601 24556862698666496760328201)
      ·
        refine ⟨18417647023999872570246151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24556862698666496760328201 18417647023999872570246151)
        ·
          refine ⟨27626470535999808855369227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18417647023999872570246151 27626470535999808855369227)
          ·
            refine ⟨41439705803999713283053841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27626470535999808855369227 41439705803999713283053841)
            ·
              refine ⟨31079779352999784962290381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41439705803999713283053841 31079779352999784962290381)
              ·
                refine ⟨11654917257374919360858893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31079779352999784962290381 11654917257374919360858893)
                ·
                  refine ⟨4370593971515594760322085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11654917257374919360858893 4370593971515594760322085)
                  ·
                    refine ⟨819486369659174017560391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4370593971515594760322085 819486369659174017560391)
                    ·
                      rfl

theorem cell22_2393916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2393916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2393916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2393916 prefixEnd_2393916 := by exact prefixLift 2393916
  have htrace : WordTrace (prefixWord ++ tailWord_2393916) baseStart_2393916 baseEnd_2393916 := by
    simpa [prefixWord, tailWord_2393916, baseEnd_2393916] using wordTrace_append hprefix tailTrace_2393916
  have hstable : (prefixWord ++ tailWord_2393916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393916).length < 2 ^ (prefixWord ++ tailWord_2393916).sum := by decide
  have hdescent : baseEnd_2393916 < baseStart_2393916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394083 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 6]
def baseStart_2394083 : Nat := 118140960795 + 2394083 * 2 ^ 59
def prefixEnd_2394083 : Nat := 4983230072969 + 3 ^ 40 * 2394083 * 2
def baseEnd_2394083 : Nat := 273181179057347082878293

theorem tailTrace_2394083 : CollatzResearch.WordTrace tailWord_2394083 prefixEnd_2394083 273181179057347082878293 := by
  unfold tailWord_2394083
  simp only [CollatzResearch.WordTrace]
  refine ⟨87319380585653642669162903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58212920390435761779441935 87319380585653642669162903)
  ·
    refine ⟨130979070878480464003744355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87319380585653642669162903 130979070878480464003744355)
    ·
      refine ⟨196468606317720696005616533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130979070878480464003744355 196468606317720696005616533)
      ·
        refine ⟨9209465921143157625263275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 196468606317720696005616533 9209465921143157625263275)
        ·
          refine ⟨13814198881714736437894913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9209465921143157625263275 13814198881714736437894913)
          ·
            refine ⟨10360649161286052328421185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13814198881714736437894913 10360649161286052328421185)
            ·
              refine ⟨7770486870964539246315889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10360649161286052328421185 7770486870964539246315889)
              ·
                refine ⟨5827865153223404434736917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7770486870964539246315889 5827865153223404434736917)
                ·
                  refine ⟨273181179057347082878293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5827865153223404434736917 273181179057347082878293)
                  ·
                    rfl

theorem cell22_2394083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_2394083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394083 prefixEnd_2394083 := by exact prefixLift 2394083
  have htrace : WordTrace (prefixWord ++ tailWord_2394083) baseStart_2394083 baseEnd_2394083 := by
    simpa [prefixWord, tailWord_2394083, baseEnd_2394083] using wordTrace_append hprefix tailTrace_2394083
  have hstable : (prefixWord ++ tailWord_2394083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394083).length < 2 ^ (prefixWord ++ tailWord_2394083).sum := by decide
  have hdescent : baseEnd_2394083 < baseStart_2394083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394093 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_2394093 : Nat := 118140960795 + 2394093 * 2 ^ 59
def prefixEnd_2394093 : Nat := 4983230072969 + 3 ^ 40 * 2394093 * 2
def baseEnd_2394093 : Nat := 819546960376404555884849

theorem tailTrace_2394093 : CollatzResearch.WordTrace tailWord_2394093 prefixEnd_2394093 819546960376404555884849 := by
  unfold tailWord_2394093
  simp only [CollatzResearch.WordTrace]
  refine ⟨87319745315617414377026933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58213163543744942918017955 87319745315617414377026933)
  ·
    refine ⟨8186226123339132597846275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87319745315617414377026933 8186226123339132597846275)
    ·
      refine ⟨12279339185008698896769413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8186226123339132597846275 12279339185008698896769413)
      ·
        refine ⟨2302376097189131043144265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12279339185008698896769413 2302376097189131043144265)
        ·
          refine ⟨1726782072891848282358199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2302376097189131043144265 1726782072891848282358199)
          ·
            refine ⟨2590173109337772423537299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726782072891848282358199 2590173109337772423537299)
            ·
              refine ⟨3885259664006658635305949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590173109337772423537299 3885259664006658635305949)
              ·
                refine ⟨1456972374002496988239731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3885259664006658635305949 1456972374002496988239731)
                ·
                  refine ⟨2185458561003745482359597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456972374002496988239731 2185458561003745482359597)
                  ·
                    refine ⟨819546960376404555884849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185458561003745482359597 819546960376404555884849)
                    ·
                      rfl

theorem cell22_2394093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_2394093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394093 prefixEnd_2394093 := by exact prefixLift 2394093
  have htrace : WordTrace (prefixWord ++ tailWord_2394093) baseStart_2394093 baseEnd_2394093 := by
    simpa [prefixWord, tailWord_2394093, baseEnd_2394093] using wordTrace_append hprefix tailTrace_2394093
  have hstable : (prefixWord ++ tailWord_2394093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394093).length < 2 ^ (prefixWord ++ tailWord_2394093).sum := by decide
  have hdescent : baseEnd_2394093 < baseStart_2394093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394117 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 4]
def baseStart_2394117 : Nat := 118140960795 + 2394117 * 2 ^ 59
def prefixEnd_2394117 : Nat := 4983230072969 + 3 ^ 40 * 2394117 * 2
def baseEnd_2394117 : Nat := 273185058688958831094925

theorem tailTrace_2394117 : CollatzResearch.WordTrace tailWord_2394117 prefixEnd_2394117 273185058688958831094925 := by
  unfold tailWord_2394117
  simp only [CollatzResearch.WordTrace]
  refine ⟨87320620667530466475900605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58213747111686977650600403 87320620667530466475900605)
  ·
    refine ⟨32745232750323924928462727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87320620667530466475900605 32745232750323924928462727)
    ·
      refine ⟨49117849125485887392694091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32745232750323924928462727 49117849125485887392694091)
      ·
        refine ⟨73676773688228831089041137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49117849125485887392694091 73676773688228831089041137)
        ·
          refine ⟨55257580266171623316780853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73676773688228831089041137 55257580266171623316780853)
          ·
            refine ⟨5180398149953589685948205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55257580266171623316780853 5180398149953589685948205)
            ·
              refine ⟨1942649306232596132230577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5180398149953589685948205 1942649306232596132230577)
              ·
                refine ⟨1456986979674447099172933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942649306232596132230577 1456986979674447099172933)
                ·
                  refine ⟨273185058688958831094925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456986979674447099172933 273185058688958831094925)
                  ·
                    rfl

theorem cell22_2394117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_2394117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394117 prefixEnd_2394117 := by exact prefixLift 2394117
  have htrace : WordTrace (prefixWord ++ tailWord_2394117) baseStart_2394117 baseEnd_2394117 := by
    simpa [prefixWord, tailWord_2394117, baseEnd_2394117] using wordTrace_append hprefix tailTrace_2394117
  have hstable : (prefixWord ++ tailWord_2394117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394117).length < 2 ^ (prefixWord ++ tailWord_2394117).sum := by decide
  have hdescent : baseEnd_2394117 < baseStart_2394117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394188 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_2394188 : Nat := 118140960795 + 2394188 * 2 ^ 59
def prefixEnd_2394188 : Nat := 4983230072969 + 3 ^ 40 * 2394188 * 2
def baseEnd_2394188 : Nat := 819579480817855974759557

theorem tailTrace_2394188 : CollatzResearch.WordTrace tailWord_2394188 prefixEnd_2394188 819579480817855974759557 := by
  unfold tailWord_2394188
  simp only [CollatzResearch.WordTrace]
  refine ⟨43661605125136622800867609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58215473500182163734490145 43661605125136622800867609)
  ·
    refine ⟨32746203843852467100650707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43661605125136622800867609 32746203843852467100650707)
    ·
      refine ⟨49119305765778700650976061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32746203843852467100650707 49119305765778700650976061)
      ·
        refine ⟨18419739662167012744116023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49119305765778700650976061 18419739662167012744116023)
        ·
          refine ⟨27629609493250519116174035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18419739662167012744116023 27629609493250519116174035)
          ·
            refine ⟨41444414239875778674261053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27629609493250519116174035 41444414239875778674261053)
            ·
              refine ⟨15541655339953417002847895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41444414239875778674261053 15541655339953417002847895)
              ·
                refine ⟨23312483009930125504271843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15541655339953417002847895 23312483009930125504271843)
                ·
                  refine ⟨34968724514895188256407765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23312483009930125504271843 34968724514895188256407765)
                  ·
                    refine ⟨819579480817855974759557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34968724514895188256407765 819579480817855974759557)
                    ·
                      rfl

theorem cell22_2394188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_2394188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394188 prefixEnd_2394188 := by exact prefixLift 2394188
  have htrace : WordTrace (prefixWord ++ tailWord_2394188) baseStart_2394188 baseEnd_2394188 := by
    simpa [prefixWord, tailWord_2394188, baseEnd_2394188] using wordTrace_append hprefix tailTrace_2394188
  have hstable : (prefixWord ++ tailWord_2394188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394188).length < 2 ^ (prefixWord ++ tailWord_2394188).sum := by decide
  have hdescent : baseEnd_2394188 < baseStart_2394188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394190 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_2394190 : Nat := 118140960795 + 2394190 * 2 ^ 59
def prefixEnd_2394190 : Nat := 4983230072969 + 3 ^ 40 * 2394190 * 2
def baseEnd_2394190 : Nat := 273193388486242878736517

theorem tailTrace_2394190 : CollatzResearch.WordTrace tailWord_2394190 prefixEnd_2394190 273193388486242878736517 := by
  unfold tailWord_2394190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915410399533249992913503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58215522130843999962205349 10915410399533249992913503)
  ·
    refine ⟨16373115599299874989370255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10915410399533249992913503 16373115599299874989370255)
    ·
      refine ⟨24559673398949812484055383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16373115599299874989370255 24559673398949812484055383)
      ·
        refine ⟨36839510098424718726083075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24559673398949812484055383 36839510098424718726083075)
        ·
          refine ⟨55259265147637078089124613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36839510098424718726083075 55259265147637078089124613)
          ·
            refine ⟨10361112215181952141710865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55259265147637078089124613 10361112215181952141710865)
            ·
              refine ⟨7770834161386464106283149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10361112215181952141710865 7770834161386464106283149)
              ·
                refine ⟨2914062810519924039856181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7770834161386464106283149 2914062810519924039856181)
                ·
                  refine ⟨273193388486242878736517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914062810519924039856181 273193388486242878736517)
                  ·
                    rfl

theorem cell22_2394190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_2394190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394190 prefixEnd_2394190 := by exact prefixLift 2394190
  have htrace : WordTrace (prefixWord ++ tailWord_2394190) baseStart_2394190 baseEnd_2394190 := by
    simpa [prefixWord, tailWord_2394190, baseEnd_2394190] using wordTrace_append hprefix tailTrace_2394190
  have hstable : (prefixWord ++ tailWord_2394190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394190).length < 2 ^ (prefixWord ++ tailWord_2394190).sum := by decide
  have hdescent : baseEnd_2394190 < baseStart_2394190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394254 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2394254 : Nat := 118140960795 + 2394254 * 2 ^ 59
def prefixEnd_2394254 : Nat := 4983230072969 + 3 ^ 40 * 2394254 * 2
def baseEnd_2394254 : Nat := 819602073966653802609355

theorem tailTrace_2394254 : CollatzResearch.WordTrace tailWord_2394254 prefixEnd_2394254 819602073966653802609355 := by
  unfold tailWord_2394254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915702183504267359204727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58217078312022759249091877 10915702183504267359204727)
  ·
    refine ⟨16373553275256401038807091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10915702183504267359204727 16373553275256401038807091)
    ·
      refine ⟨24560329912884601558210637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16373553275256401038807091 24560329912884601558210637)
      ·
        refine ⟨9210123717331725584328989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24560329912884601558210637 9210123717331725584328989)
        ·
          refine ⟨3453796393999397094123371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9210123717331725584328989 3453796393999397094123371)
          ·
            refine ⟨5180694590999095641185057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453796393999397094123371 5180694590999095641185057)
            ·
              refine ⟨3885520943249321730888793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5180694590999095641185057 3885520943249321730888793)
              ·
                refine ⟨2914140707436991298166595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3885520943249321730888793 2914140707436991298166595)
                ·
                  refine ⟨4371211061155486947249893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914140707436991298166595 4371211061155486947249893)
                  ·
                    refine ⟨819602073966653802609355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4371211061155486947249893 819602073966653802609355)
                    ·
                      rfl

theorem cell22_2394254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2394254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394254 prefixEnd_2394254 := by exact prefixLift 2394254
  have htrace : WordTrace (prefixWord ++ tailWord_2394254) baseStart_2394254 baseEnd_2394254 := by
    simpa [prefixWord, tailWord_2394254, baseEnd_2394254] using wordTrace_append hprefix tailTrace_2394254
  have hstable : (prefixWord ++ tailWord_2394254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394254).length < 2 ^ (prefixWord ++ tailWord_2394254).sum := by decide
  have hdescent : baseEnd_2394254 < baseStart_2394254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394269 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 4]
def baseStart_2394269 : Nat := 118140960795 + 2394269 * 2 ^ 59
def prefixEnd_2394269 : Nat := 4983230072969 + 3 ^ 40 * 2394269 * 2
def baseEnd_2394269 : Nat := 273202402924399587828103

theorem tailTrace_2394269 : CollatzResearch.WordTrace tailWord_2394269 prefixEnd_2394269 273202402924399587828103 := by
  unfold tailWord_2394269
  simp only [CollatzResearch.WordTrace]
  refine ⟨87326164562979796435433861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58217443041986530956955907 87326164562979796435433861)
  ·
    refine ⟨16373655855558711831643849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87326164562979796435433861 16373655855558711831643849)
    ·
      refine ⟨12280241891669033873732887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16373655855558711831643849 12280241891669033873732887)
      ·
        refine ⟨18420362837503550810599331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280241891669033873732887 18420362837503550810599331)
        ·
          refine ⟨27630544256255326215898997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18420362837503550810599331 27630544256255326215898997)
          ·
            refine ⟨2590363524023936832740531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27630544256255326215898997 2590363524023936832740531)
            ·
              refine ⟨3885545286035905249110797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590363524023936832740531 3885545286035905249110797)
              ·
                refine ⟨1457079482263464468416549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3885545286035905249110797 1457079482263464468416549)
                ·
                  refine ⟨273202402924399587828103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457079482263464468416549 273202402924399587828103)
                  ·
                    rfl

theorem cell22_2394269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_2394269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394269 prefixEnd_2394269 := by exact prefixLift 2394269
  have htrace : WordTrace (prefixWord ++ tailWord_2394269) baseStart_2394269 baseEnd_2394269 := by
    simpa [prefixWord, tailWord_2394269, baseEnd_2394269] using wordTrace_append hprefix tailTrace_2394269
  have hstable : (prefixWord ++ tailWord_2394269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394269).length < 2 ^ (prefixWord ++ tailWord_2394269).sum := by decide
  have hdescent : baseEnd_2394269 < baseStart_2394269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394286 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_2394286 : Nat := 118140960795 + 2394286 * 2 ^ 59
def prefixEnd_2394286 : Nat := 4983230072969 + 3 ^ 40 * 2394286 * 2
def baseEnd_2394286 : Nat := 273204342740205461936419

theorem tailTrace_2394286 : CollatzResearch.WordTrace tailWord_2394286 prefixEnd_2394286 273204342740205461936419 := by
  unfold tailWord_2394286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915848075489776042350339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58217856402612138892535141 10915848075489776042350339)
  ·
    refine ⟨16373772113234664063525509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10915848075489776042350339 16373772113234664063525509)
    ·
      refine ⟨3070082271231499511911033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16373772113234664063525509 3070082271231499511911033)
      ·
        refine ⟨2302561703423624633933275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3070082271231499511911033 2302561703423624633933275)
        ·
          refine ⟨3453842555135436950899913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302561703423624633933275 3453842555135436950899913)
          ·
            refine ⟨2590381916351577713174935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453842555135436950899913 2590381916351577713174935)
            ·
              refine ⟨3885572874527366569762403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590381916351577713174935 3885572874527366569762403)
              ·
                refine ⟨5828359311791049854643605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3885572874527366569762403 5828359311791049854643605)
                ·
                  refine ⟨273204342740205461936419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5828359311791049854643605 273204342740205461936419)
                  ·
                    rfl

theorem cell22_2394286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_2394286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394286 prefixEnd_2394286 := by exact prefixLift 2394286
  have htrace : WordTrace (prefixWord ++ tailWord_2394286) baseStart_2394286 baseEnd_2394286 := by
    simpa [prefixWord, tailWord_2394286, baseEnd_2394286] using wordTrace_append hprefix tailTrace_2394286
  have hstable : (prefixWord ++ tailWord_2394286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394286).length < 2 ^ (prefixWord ++ tailWord_2394286).sum := by decide
  have hdescent : baseEnd_2394286 < baseStart_2394286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394340 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_2394340 : Nat := 118140960795 + 2394340 * 2 ^ 59
def prefixEnd_2394340 : Nat := 4983230072969 + 3 ^ 40 * 2394340 * 2
def baseEnd_2394340 : Nat := 819631513524178244959091

theorem tailTrace_2394340 : CollatzResearch.WordTrace tailWord_2394340 prefixEnd_2394340 819631513524178244959091 := by
  unfold tailWord_2394340
  simp only [CollatzResearch.WordTrace]
  refine ⟨43664377072861287780634237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58219169430481717040845649 43664377072861287780634237)
  ·
    refine ⟨16374141402322982917737839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43664377072861287780634237 16374141402322982917737839)
    ·
      refine ⟨24561212103484474376606759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16374141402322982917737839 24561212103484474376606759)
      ·
        refine ⟨36841818155226711564910139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24561212103484474376606759 36841818155226711564910139)
        ·
          refine ⟨55262727232840067347365209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36841818155226711564910139 55262727232840067347365209)
          ·
            refine ⟨41447045424630050510523907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55262727232840067347365209 41447045424630050510523907)
            ·
              refine ⟨62170568136945075765785861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41447045424630050510523907 62170568136945075765785861)
              ·
                refine ⟨11656981525677201706084849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62170568136945075765785861 11656981525677201706084849)
                ·
                  refine ⟨8742736144257901279563637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11656981525677201706084849 8742736144257901279563637)
                  ·
                    refine ⟨819631513524178244959091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8742736144257901279563637 819631513524178244959091)
                    ·
                      rfl

theorem cell22_2394340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_2394340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394340 prefixEnd_2394340 := by exact prefixLift 2394340
  have htrace : WordTrace (prefixWord ++ tailWord_2394340) baseStart_2394340 baseEnd_2394340 := by
    simpa [prefixWord, tailWord_2394340, baseEnd_2394340] using wordTrace_append hprefix tailTrace_2394340
  have hstable : (prefixWord ++ tailWord_2394340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394340).length < 2 ^ (prefixWord ++ tailWord_2394340).sum := by decide
  have hdescent : baseEnd_2394340 < baseStart_2394340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394355 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 5, 4]
def baseStart_2394355 : Nat := 118140960795 + 2394355 * 2 ^ 59
def prefixEnd_2394355 : Nat := 4983230072969 + 3 ^ 40 * 2394355 * 2
def baseEnd_2394355 : Nat := 819636648330723205834045

theorem tailTrace_2394355 : CollatzResearch.WordTrace tailWord_2394355 prefixEnd_2394355 819636648330723205834045 := by
  unfold tailWord_2394355
  simp only [CollatzResearch.WordTrace]
  refine ⟨87329301240668233123064519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58219534160445488748709679 87329301240668233123064519)
  ·
    refine ⟨130993951861002349684596779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87329301240668233123064519 130993951861002349684596779)
    ·
      refine ⟨196490927791503524526895169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130993951861002349684596779 196490927791503524526895169)
      ·
        refine ⟨147368195843627643395171377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196490927791503524526895169 147368195843627643395171377)
        ·
          refine ⟨110526146882720732546378533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147368195843627643395171377 110526146882720732546378533)
          ·
            refine ⟨20723652540510137352445975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110526146882720732546378533 20723652540510137352445975)
            ·
              refine ⟨31085478810765206028668963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20723652540510137352445975 31085478810765206028668963)
              ·
                refine ⟨46628218216147809043003445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31085478810765206028668963 46628218216147809043003445)
                ·
                  refine ⟨4371395457763857097781573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46628218216147809043003445 4371395457763857097781573)
                  ·
                    refine ⟨819636648330723205834045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4371395457763857097781573 819636648330723205834045)
                    ·
                      rfl

theorem cell22_2394355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_2394355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394355 prefixEnd_2394355 := by exact prefixLift 2394355
  have htrace : WordTrace (prefixWord ++ tailWord_2394355) baseStart_2394355 baseEnd_2394355 := by
    simpa [prefixWord, tailWord_2394355, baseEnd_2394355] using wordTrace_append hprefix tailTrace_2394355
  have hstable : (prefixWord ++ tailWord_2394355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394355).length < 2 ^ (prefixWord ++ tailWord_2394355).sum := by decide
  have hdescent : baseEnd_2394355 < baseStart_2394355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394389 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_2394389 : Nat := 118140960795 + 2394389 * 2 ^ 59
def prefixEnd_2394389 : Nat := 4983230072969 + 3 ^ 40 * 2394389 * 2
def baseEnd_2394389 : Nat := 819648287225558450483941

theorem tailTrace_2394389 : CollatzResearch.WordTrace tailWord_2394389 prefixEnd_2394389 819648287225558450483941 := by
  unfold tailWord_2394389
  simp only [CollatzResearch.WordTrace]
  refine ⟨87330541322545056929802221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58220360881696704619868147 87330541322545056929802221)
  ·
    refine ⟨32748952995954396348675833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87330541322545056929802221 32748952995954396348675833)
    ·
      refine ⟨24561714746965797261506875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32748952995954396348675833 24561714746965797261506875)
      ·
        refine ⟨36842572120448695892260313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24561714746965797261506875 36842572120448695892260313)
        ·
          refine ⟨27631929090336521919195235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36842572120448695892260313 27631929090336521919195235)
          ·
            refine ⟨41447893635504782878792853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27631929090336521919195235 41447893635504782878792853)
            ·
              refine ⟨1942870014164286697443415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41447893635504782878792853 1942870014164286697443415)
              ·
                refine ⟨2914305021246430046165123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1942870014164286697443415 2914305021246430046165123)
                ·
                  refine ⟨4371457531869645069247685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914305021246430046165123 4371457531869645069247685)
                  ·
                    refine ⟨819648287225558450483941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4371457531869645069247685 819648287225558450483941)
                    ·
                      rfl

theorem cell22_2394389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_2394389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394389 prefixEnd_2394389 := by exact prefixLift 2394389
  have htrace : WordTrace (prefixWord ++ tailWord_2394389) baseStart_2394389 baseEnd_2394389 := by
    simpa [prefixWord, tailWord_2394389, baseEnd_2394389] using wordTrace_append hprefix tailTrace_2394389
  have hstable : (prefixWord ++ tailWord_2394389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394389).length < 2 ^ (prefixWord ++ tailWord_2394389).sum := by decide
  have hdescent : baseEnd_2394389 < baseStart_2394389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394404 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 4]
def baseStart_2394404 : Nat := 118140960795 + 2394404 * 2 ^ 59
def prefixEnd_2394404 : Nat := 4983230072969 + 3 ^ 40 * 2394404 * 2
def baseEnd_2394404 : Nat := 273217807344034470452965

theorem tailTrace_2394404 : CollatzResearch.WordTrace tailWord_2394404 prefixEnd_2394404 273217807344034470452965 := by
  unfold tailWord_2394404
  simp only [CollatzResearch.WordTrace]
  refine ⟨43665544208745357245799133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58220725611660476327732177 43665544208745357245799133)
  ·
    refine ⟨16374579078279508967174675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43665544208745357245799133 16374579078279508967174675)
    ·
      refine ⟨24561868617419263450762013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16374579078279508967174675 24561868617419263450762013)
      ·
        refine ⟨9210700731532223794035755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24561868617419263450762013 9210700731532223794035755)
        ·
          refine ⟨13816051097298335691053633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9210700731532223794035755 13816051097298335691053633)
          ·
            refine ⟨10362038322973751768290225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13816051097298335691053633 10362038322973751768290225)
            ·
              refine ⟨7771528742230313826217669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10362038322973751768290225 7771528742230313826217669)
              ·
                refine ⟨1457161639168183842415813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7771528742230313826217669 1457161639168183842415813)
                ·
                  refine ⟨273217807344034470452965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457161639168183842415813 273217807344034470452965)
                  ·
                    rfl

theorem cell22_2394404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_2394404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394404 prefixEnd_2394404 := by exact prefixLift 2394404
  have htrace : WordTrace (prefixWord ++ tailWord_2394404) baseStart_2394404 baseEnd_2394404 := by
    simpa [prefixWord, tailWord_2394404, baseEnd_2394404] using wordTrace_append hprefix tailTrace_2394404
  have hstable : (prefixWord ++ tailWord_2394404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394404).length < 2 ^ (prefixWord ++ tailWord_2394404).sum := by decide
  have hdescent : baseEnd_2394404 < baseStart_2394404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394526 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2394526 : Nat := 118140960795 + 2394526 * 2 ^ 59
def prefixEnd_2394526 : Nat := 4983230072969 + 3 ^ 40 * 2394526 * 2
def baseEnd_2394526 : Nat := 819695185125335759808521

theorem tailTrace_2394526 : CollatzResearch.WordTrace tailWord_2394526 prefixEnd_2394526 819695185125335759808521 := by
  unfold tailWord_2394526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916942265381091165942429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58223692082032486218359621 10916942265381091165942429)
  ·
    refine ⟨4093853349517909187228411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10916942265381091165942429 4093853349517909187228411)
    ·
      refine ⟨6140780024276863780842617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4093853349517909187228411 6140780024276863780842617)
      ·
        refine ⟨4605585018207647835631963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6140780024276863780842617 4605585018207647835631963)
        ·
          refine ⟨6908377527311471753447945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605585018207647835631963 6908377527311471753447945)
          ·
            refine ⟨5181283145483603815085959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6908377527311471753447945 5181283145483603815085959)
            ·
              refine ⟨7771924718225405722628939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181283145483603815085959 7771924718225405722628939)
              ·
                refine ⟨11657887077338108583943409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7771924718225405722628939 11657887077338108583943409)
                ·
                  refine ⟨8743415308003581437957557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11657887077338108583943409 8743415308003581437957557)
                  ·
                    refine ⟨819695185125335759808521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8743415308003581437957557 819695185125335759808521)
                    ·
                      rfl

theorem cell22_2394526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2394526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394526 prefixEnd_2394526 := by exact prefixLift 2394526
  have htrace : WordTrace (prefixWord ++ tailWord_2394526) baseStart_2394526 baseEnd_2394526 := by
    simpa [prefixWord, tailWord_2394526, baseEnd_2394526] using wordTrace_append hprefix tailTrace_2394526
  have hstable : (prefixWord ++ tailWord_2394526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394526).length < 2 ^ (prefixWord ++ tailWord_2394526).sum := by decide
  have hdescent : baseEnd_2394526 < baseStart_2394526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394556 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 4]
def baseStart_2394556 : Nat := 118140960795 + 2394556 * 2 ^ 59
def prefixEnd_2394556 : Nat := 4983230072969 + 3 ^ 40 * 2394556 * 2
def baseEnd_2394556 : Nat := 273235151579475227186143

theorem tailTrace_2394556 : CollatzResearch.WordTrace tailWord_2394556 prefixEnd_2394556 273235151579475227186143 := by
  unfold tailWord_2394556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43668316156470022225565761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58224421541960029634087681 43668316156470022225565761)
  ·
    refine ⟨32751237117352516669174321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43668316156470022225565761 32751237117352516669174321)
    ·
      refine ⟨24563427838014387501880741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32751237117352516669174321 24563427838014387501880741)
      ·
        refine ⟨4605642719627697656602639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24563427838014387501880741 4605642719627697656602639)
        ·
          refine ⟨6908464079441546484903959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605642719627697656602639 6908464079441546484903959)
          ·
            refine ⟨10362696119162319727355939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6908464079441546484903959 10362696119162319727355939)
            ·
              refine ⟨15544044178743479591033909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10362696119162319727355939 15544044178743479591033909)
              ·
                refine ⟨1457254141757201211659429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15544044178743479591033909 1457254141757201211659429)
                ·
                  refine ⟨273235151579475227186143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457254141757201211659429 273235151579475227186143)
                  ·
                    rfl

theorem cell22_2394556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_2394556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394556 prefixEnd_2394556 := by exact prefixLift 2394556
  have htrace : WordTrace (prefixWord ++ tailWord_2394556) baseStart_2394556 baseEnd_2394556 := by
    simpa [prefixWord, tailWord_2394556, baseEnd_2394556] using wordTrace_append hprefix tailTrace_2394556
  have hstable : (prefixWord ++ tailWord_2394556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394556).length < 2 ^ (prefixWord ++ tailWord_2394556).sum := by decide
  have hdescent : baseEnd_2394556 < baseStart_2394556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394567 : List Nat := [1, 1, 4, 1, 1, 5, 9]
def baseStart_2394567 : Nat := 118140960795 + 2394567 * 2 ^ 59
def prefixEnd_2394567 : Nat := 4983230072969 + 3 ^ 40 * 2394567 * 2
def baseEnd_2394567 : Nat := 30359600750489826649385

theorem tailTrace_2394567 : CollatzResearch.WordTrace tailWord_2394567 prefixEnd_2394567 30359600750489826649385 := by
  unfold tailWord_2394567
  simp only [CollatzResearch.WordTrace]
  refine ⟨87337033515900193329781955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58224689010600128886521303 87337033515900193329781955)
  ·
    refine ⟨131005550273850289994672933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87337033515900193329781955 131005550273850289994672933)
    ·
      refine ⟨24563540676346929374001175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131005550273850289994672933 24563540676346929374001175)
      ·
        refine ⟨36845311014520394061001763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24563540676346929374001175 36845311014520394061001763)
        ·
          refine ⟨55267966521780591091502645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36845311014520394061001763 55267966521780591091502645)
          ·
            refine ⟨5181371861416930414828373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55267966521780591091502645 5181371861416930414828373)
            ·
              refine ⟨30359600750489826649385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5181371861416930414828373 30359600750489826649385)
              ·
                rfl

theorem cell22_2394567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 9].length) (baseStart_2394567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394567 prefixEnd_2394567 := by exact prefixLift 2394567
  have htrace : WordTrace (prefixWord ++ tailWord_2394567) baseStart_2394567 baseEnd_2394567 := by
    simpa [prefixWord, tailWord_2394567, baseEnd_2394567] using wordTrace_append hprefix tailTrace_2394567
  have hstable : (prefixWord ++ tailWord_2394567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394567).length < 2 ^ (prefixWord ++ tailWord_2394567).sum := by decide
  have hdescent : baseEnd_2394567 < baseStart_2394567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394706 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2394706 : Nat := 118140960795 + 2394706 * 2 ^ 59
def prefixEnd_2394706 : Nat := 4983230072969 + 3 ^ 40 * 2394706 * 2
def baseEnd_2394706 : Nat := 819756802803875290307969

theorem tailTrace_2394706 : CollatzResearch.WordTrace tailWord_2394706 prefixEnd_2394706 819756802803875290307969 := by
  unfold tailWord_2394706
  simp only [CollatzResearch.WordTrace]
  refine ⟨21835525815599155017272993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58228068841597746712727981 21835525815599155017272993)
  ·
    refine ⟨16376644361699366262954745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21835525815599155017272993 16376644361699366262954745)
    ·
      refine ⟨12282483271274524697216059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16376644361699366262954745 12282483271274524697216059)
      ·
        refine ⟨18423724906911787045824089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12282483271274524697216059 18423724906911787045824089)
        ·
          refine ⟨13817793680183840284368067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18423724906911787045824089 13817793680183840284368067)
          ·
            refine ⟨20726690520275760426552101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13817793680183840284368067 20726690520275760426552101)
            ·
              refine ⟨3886254472551705079978519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20726690520275760426552101 3886254472551705079978519)
              ·
                refine ⟨5829381708827557619967779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886254472551705079978519 5829381708827557619967779)
                ·
                  refine ⟨8744072563241336429951669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5829381708827557619967779 8744072563241336429951669)
                  ·
                    refine ⟨819756802803875290307969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8744072563241336429951669 819756802803875290307969)
                    ·
                      rfl

theorem cell22_2394706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2394706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394706 prefixEnd_2394706 := by exact prefixLift 2394706
  have htrace : WordTrace (prefixWord ++ tailWord_2394706) baseStart_2394706 baseEnd_2394706 := by
    simpa [prefixWord, tailWord_2394706, baseEnd_2394706] using wordTrace_append hprefix tailTrace_2394706
  have hstable : (prefixWord ++ tailWord_2394706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394706).length < 2 ^ (prefixWord ++ tailWord_2394706).sum := by decide
  have hdescent : baseEnd_2394706 < baseStart_2394706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394721 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2394721 : Nat := 118140960795 + 2394721 * 2 ^ 59
def prefixEnd_2394721 : Nat := 4983230072969 + 3 ^ 40 * 2394721 * 2
def baseEnd_2394721 : Nat := 819761937610420251182923

theorem tailTrace_2394721 : CollatzResearch.WordTrace tailWord_2394721 prefixEnd_2394721 819761937610420251182923 := by
  unfold tailWord_2394721
  simp only [CollatzResearch.WordTrace]
  refine ⟨87342650357342277630888017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58228433571561518420592011 87342650357342277630888017)
  ·
    refine ⟨65506987768006708223166013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87342650357342277630888017 65506987768006708223166013)
    ·
      refine ⟨24565120413002515583687255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65506987768006708223166013 24565120413002515583687255)
      ·
        refine ⟨36847680619503773375530883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24565120413002515583687255 36847680619503773375530883)
        ·
          refine ⟨55271520929255660063296325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36847680619503773375530883 55271520929255660063296325)
          ·
            refine ⟨10363410174235436261868061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55271520929255660063296325 10363410174235436261868061)
            ·
              refine ⟨3886278815338288598200523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10363410174235436261868061 3886278815338288598200523)
              ·
                refine ⟨5829418223007432897300785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886278815338288598200523 5829418223007432897300785)
                ·
                  refine ⟨4372063667255574672975589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5829418223007432897300785 4372063667255574672975589)
                  ·
                    refine ⟨819761937610420251182923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4372063667255574672975589 819761937610420251182923)
                    ·
                      rfl

theorem cell22_2394721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2394721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394721 prefixEnd_2394721 := by exact prefixLift 2394721
  have htrace : WordTrace (prefixWord ++ tailWord_2394721) baseStart_2394721 baseEnd_2394721 := by
    simpa [prefixWord, tailWord_2394721, baseEnd_2394721] using wordTrace_append hprefix tailTrace_2394721
  have hstable : (prefixWord ++ tailWord_2394721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394721).length < 2 ^ (prefixWord ++ tailWord_2394721).sum := by decide
  have hdescent : baseEnd_2394721 < baseStart_2394721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394798 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_2394798 : Nat := 118140960795 + 2394798 * 2 ^ 59
def prefixEnd_2394798 : Nat := 4983230072969 + 3 ^ 40 * 2394798 * 2
def baseEnd_2394798 : Nat := 273262765428005905669229

theorem tailTrace_2394798 : CollatzResearch.WordTrace tailWord_2394798 prefixEnd_2394798 273262765428005905669229 := by
  unfold tailWord_2394798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918182347257914972680131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58230305852042213187627365 10918182347257914972680131)
  ·
    refine ⟨16377273520886872459020197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10918182347257914972680131 16377273520886872459020197)
    ·
      refine ⟨3070738785166288586066287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16377273520886872459020197 3070738785166288586066287)
      ·
        refine ⟨4606108177749432879099431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070738785166288586066287 4606108177749432879099431)
        ·
          refine ⟨6909162266624149318649147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606108177749432879099431 6909162266624149318649147)
          ·
            refine ⟨10363743399936223977973721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6909162266624149318649147 10363743399936223977973721)
            ·
              refine ⟨7772807549952167983480291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10363743399936223977973721 7772807549952167983480291)
              ·
                refine ⟨11659211324928251975220437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7772807549952167983480291 11659211324928251975220437)
                ·
                  refine ⟨273262765428005905669229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11659211324928251975220437 273262765428005905669229)
                  ·
                    rfl

theorem cell22_2394798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_2394798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394798 prefixEnd_2394798 := by exact prefixLift 2394798
  have htrace : WordTrace (prefixWord ++ tailWord_2394798) baseStart_2394798 baseEnd_2394798 := by
    simpa [prefixWord, tailWord_2394798, baseEnd_2394798] using wordTrace_append hprefix tailTrace_2394798
  have hstable : (prefixWord ++ tailWord_2394798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394798).length < 2 ^ (prefixWord ++ tailWord_2394798).sum := by decide
  have hdescent : baseEnd_2394798 < baseStart_2394798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394828 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_2394828 : Nat := 118140960795 + 2394828 * 2 ^ 59
def prefixEnd_2394828 : Nat := 4983230072969 + 3 ^ 40 * 2394828 * 2
def baseEnd_2394828 : Nat := 819798565897107638757595

theorem tailTrace_2394828 : CollatzResearch.WordTrace tailWord_2394828 prefixEnd_2394828 819798565897107638757595 := by
  unfold tailWord_2394828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43673276483977317452516569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58231035311969756603355425 43673276483977317452516569)
  ·
    refine ⟨32754957362982988089387427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43673276483977317452516569 32754957362982988089387427)
    ·
      refine ⟨49132436044474482134081141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32754957362982988089387427 49132436044474482134081141)
      ·
        refine ⟨4606165879169482700070107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49132436044474482134081141 4606165879169482700070107)
        ·
          refine ⟨6909248818754224050105161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606165879169482700070107 6909248818754224050105161)
          ·
            refine ⟨5181936614065668037578871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6909248818754224050105161 5181936614065668037578871)
            ·
              refine ⟨7772904921098502056368307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181936614065668037578871 7772904921098502056368307)
              ·
                refine ⟨11659357381647753084552461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7772904921098502056368307 11659357381647753084552461)
                ·
                  refine ⟨4372259018117907406707173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11659357381647753084552461 4372259018117907406707173)
                  ·
                    refine ⟨819798565897107638757595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4372259018117907406707173 819798565897107638757595)
                    ·
                      rfl

theorem cell22_2394828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_2394828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394828 prefixEnd_2394828 := by exact prefixLift 2394828
  have htrace : WordTrace (prefixWord ++ tailWord_2394828) baseStart_2394828 baseEnd_2394828 := by
    simpa [prefixWord, tailWord_2394828, baseEnd_2394828] using wordTrace_append hprefix tailTrace_2394828
  have hstable : (prefixWord ++ tailWord_2394828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394828).length < 2 ^ (prefixWord ++ tailWord_2394828).sum := by decide
  have hdescent : baseEnd_2394828 < baseStart_2394828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394841 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_2394841 : Nat := 118140960795 + 2394841 * 2 ^ 59
def prefixEnd_2394841 : Nat := 4983230072969 + 3 ^ 40 * 2394841 * 2
def baseEnd_2394841 : Nat := 819803016062779938182555

theorem tailTrace_2394841 : CollatzResearch.WordTrace tailWord_2394841 prefixEnd_2394841 819803016062779938182555 := by
  unfold tailWord_2394841
  simp only [CollatzResearch.WordTrace]
  refine ⟨87347027116907538125256377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58231351411271692083504251 87347027116907538125256377)
  ·
    refine ⟨65510270337680653593942283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87347027116907538125256377 65510270337680653593942283)
    ·
      refine ⟨98265405506520980390913425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65510270337680653593942283 98265405506520980390913425)
      ·
        refine ⟨73699054129890735293185069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98265405506520980390913425 73699054129890735293185069)
        ·
          refine ⟨27637145298709025734944401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73699054129890735293185069 27637145298709025734944401)
          ·
            refine ⟨20727858974031769301208301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27637145298709025734944401 20727858974031769301208301)
            ·
              refine ⟨7772947115261913487953113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20727858974031769301208301 7772947115261913487953113)
              ·
                refine ⟨5829710336446435115964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7772947115261913487953113 5829710336446435115964835)
                ·
                  refine ⟨8744565504669652673947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5829710336446435115964835 8744565504669652673947253)
                  ·
                    refine ⟨819803016062779938182555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8744565504669652673947253 819803016062779938182555)
                    ·
                      rfl

theorem cell22_2394841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_2394841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394841 prefixEnd_2394841 := by exact prefixLift 2394841
  have htrace : WordTrace (prefixWord ++ tailWord_2394841) baseStart_2394841 baseEnd_2394841 := by
    simpa [prefixWord, tailWord_2394841, baseEnd_2394841] using wordTrace_append hprefix tailTrace_2394841
  have hstable : (prefixWord ++ tailWord_2394841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394841).length < 2 ^ (prefixWord ++ tailWord_2394841).sum := by decide
  have hdescent : baseEnd_2394841 < baseStart_2394841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394888 : List Nat := [2, 1, 3, 2, 2, 3, 3, 6]
def baseStart_2394888 : Nat := 118140960795 + 2394888 * 2 ^ 59
def prefixEnd_2394888 : Nat := 4983230072969 + 3 ^ 40 * 2394888 * 2
def baseEnd_2394888 : Nat := 91091011680365275806379

theorem tailTrace_2394888 : CollatzResearch.WordTrace tailWord_2394888 prefixEnd_2394888 91091011680365275806379 := by
  unfold tailWord_2394888
  simp only [CollatzResearch.WordTrace]
  refine ⟨43674370673868632576108659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58232494231824843434811545 43674370673868632576108659)
  ·
    refine ⟨65511556010802948864162989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43674370673868632576108659 65511556010802948864162989)
    ·
      refine ⟨24566833504051105824061121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65511556010802948864162989 24566833504051105824061121)
      ·
        refine ⟨18425125128038329368045841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24566833504051105824061121 18425125128038329368045841)
        ·
          refine ⟨13818843846028747026034381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18425125128038329368045841 13818843846028747026034381)
          ·
            refine ⟨5182066442260780134762893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13818843846028747026034381 5182066442260780134762893)
            ·
              refine ⟨1943274915847792550536085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5182066442260780134762893 1943274915847792550536085)
              ·
                refine ⟨91091011680365275806379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1943274915847792550536085 91091011680365275806379)
                ·
                  rfl

theorem cell22_2394888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_2394888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394888 prefixEnd_2394888 := by exact prefixLift 2394888
  have htrace : WordTrace (prefixWord ++ tailWord_2394888) baseStart_2394888 baseEnd_2394888 := by
    simpa [prefixWord, tailWord_2394888, baseEnd_2394888] using wordTrace_append hprefix tailTrace_2394888
  have hstable : (prefixWord ++ tailWord_2394888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394888).length < 2 ^ (prefixWord ++ tailWord_2394888).sum := by decide
  have hdescent : baseEnd_2394888 < baseStart_2394888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394909 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2394909 : Nat := 118140960795 + 2394909 * 2 ^ 59
def prefixEnd_2394909 : Nat := 4983230072969 + 3 ^ 40 * 2394909 * 2
def baseEnd_2394909 : Nat := 819826293852450427482347

theorem tailTrace_2394909 : CollatzResearch.WordTrace tailWord_2394909 prefixEnd_2394909 819826293852450427482347 := by
  unfold tailWord_2394909
  simp only [CollatzResearch.WordTrace]
  refine ⟨87349507280661185738731781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58233004853774123825821187 87349507280661185738731781)
  ·
    refine ⟨16378032615123972326012209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87349507280661185738731781 16378032615123972326012209)
    ·
      refine ⟨12283524461342979244509157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16378032615123972326012209 12283524461342979244509157)
      ·
        refine ⟨2303160836501808608345467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12283524461342979244509157 2303160836501808608345467)
        ·
          refine ⟨3454741254752712912518201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303160836501808608345467 3454741254752712912518201)
          ·
            refine ⟨2591055941064534684388651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3454741254752712912518201 2591055941064534684388651)
            ·
              refine ⟨3886583911596802026582977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591055941064534684388651 3886583911596802026582977)
              ·
                refine ⟨2914937933697601519937233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3886583911596802026582977 2914937933697601519937233)
                ·
                  refine ⟨2186203450273201139952925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2914937933697601519937233 2186203450273201139952925)
                  ·
                    refine ⟨819826293852450427482347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186203450273201139952925 819826293852450427482347)
                    ·
                      rfl

theorem cell22_2394909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2394909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394909 prefixEnd_2394909 := by exact prefixLift 2394909
  have htrace : WordTrace (prefixWord ++ tailWord_2394909) baseStart_2394909 baseEnd_2394909 := by
    simpa [prefixWord, tailWord_2394909, baseEnd_2394909] using wordTrace_append hprefix tailTrace_2394909
  have hstable : (prefixWord ++ tailWord_2394909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394909).length < 2 ^ (prefixWord ++ tailWord_2394909).sum := by decide
  have hdescent : baseEnd_2394909 < baseStart_2394909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394920 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2394920 : Nat := 118140960795 + 2394920 * 2 ^ 59
def prefixEnd_2394920 : Nat := 4983230072969 + 3 ^ 40 * 2394920 * 2
def baseEnd_2394920 : Nat := 819830059377250065457313

theorem tailTrace_2394920 : CollatzResearch.WordTrace tailWord_2394920 prefixEnd_2394920 819830059377250065457313 := by
  unfold tailWord_2394920
  simp only [CollatzResearch.WordTrace]
  refine ⟨43674954241810667308691107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58233272322414223078254809 43674954241810667308691107)
  ·
    refine ⟨65512431362716000963036661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43674954241810667308691107 65512431362716000963036661)
    ·
      refine ⟨6141790440254625090284687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65512431362716000963036661 6141790440254625090284687)
      ·
        refine ⟨9212685660381937635427031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6141790440254625090284687 9212685660381937635427031)
        ·
          refine ⟨13819028490572906453140547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212685660381937635427031 13819028490572906453140547)
          ·
            refine ⟨20728542735859359679710821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13819028490572906453140547 20728542735859359679710821)
            ·
              refine ⟨3886601762973629939945779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20728542735859359679710821 3886601762973629939945779)
              ·
                refine ⟨5829902644460444909918669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886601762973629939945779 5829902644460444909918669)
                ·
                  refine ⟨2186213491672666841219501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5829902644460444909918669 2186213491672666841219501)
                  ·
                    refine ⟨819830059377250065457313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186213491672666841219501 819830059377250065457313)
                    ·
                      rfl

theorem cell22_2394920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2394920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394920 prefixEnd_2394920 := by exact prefixLift 2394920
  have htrace : WordTrace (prefixWord ++ tailWord_2394920) baseStart_2394920 baseEnd_2394920 := by
    simpa [prefixWord, tailWord_2394920, baseEnd_2394920] using wordTrace_append hprefix tailTrace_2394920
  have hstable : (prefixWord ++ tailWord_2394920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394920).length < 2 ^ (prefixWord ++ tailWord_2394920).sum := by decide
  have hdescent : baseEnd_2394920 < baseStart_2394920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394991 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_2394991 : Nat := 118140960795 + 2394991 * 2 ^ 59
def prefixEnd_2394991 : Nat := 4983230072969 + 3 ^ 40 * 2394991 * 2
def baseEnd_2394991 : Nat := 819854364128229546932095

theorem tailTrace_2394991 : CollatzResearch.WordTrace tailWord_2394991 prefixEnd_2394991 819854364128229546932095 := by
  unfold tailWord_2394991
  simp only [CollatzResearch.WordTrace]
  refine ⟨87352498066364113743216827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58234998710909409162144551 87352498066364113743216827)
  ·
    refine ⟨131028747099546170614825241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87352498066364113743216827 131028747099546170614825241)
    ·
      refine ⟨98271560324659627961118931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131028747099546170614825241 98271560324659627961118931)
      ·
        refine ⟨147407340486989441941678397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98271560324659627961118931 147407340486989441941678397)
        ·
          refine ⟨55277752682621040728129399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147407340486989441941678397 55277752682621040728129399)
          ·
            refine ⟨82916629023931561092194099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55277752682621040728129399 82916629023931561092194099)
            ·
              refine ⟨124374943535897341638291149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82916629023931561092194099 124374943535897341638291149)
              ·
                refine ⟨46640603825961503114359181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124374943535897341638291149 46640603825961503114359181)
                ·
                  refine ⟨17490226434735563667884693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46640603825961503114359181 17490226434735563667884693)
                  ·
                    refine ⟨819854364128229546932095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17490226434735563667884693 819854364128229546932095)
                    ·
                      rfl

theorem cell22_2394991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_2394991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394991 prefixEnd_2394991 := by exact prefixLift 2394991
  have htrace : WordTrace (prefixWord ++ tailWord_2394991) baseStart_2394991 baseEnd_2394991 := by
    simpa [prefixWord, tailWord_2394991, baseEnd_2394991] using wordTrace_append hprefix tailTrace_2394991
  have hstable : (prefixWord ++ tailWord_2394991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394991).length < 2 ^ (prefixWord ++ tailWord_2394991).sum := by decide
  have hdescent : baseEnd_2394991 < baseStart_2394991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394997 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2394997 : Nat := 118140960795 + 2394997 * 2 ^ 59
def prefixEnd_2394997 : Nat := 4983230072969 + 3 ^ 40 * 2394997 * 2
def baseEnd_2394997 : Nat := 819856418050847531282077

theorem tailTrace_2394997 : CollatzResearch.WordTrace tailWord_2394997 prefixEnd_2394997 819856418050847531282077 := by
  unfold tailWord_2394997
  simp only [CollatzResearch.WordTrace]
  refine ⟨87352716904342376767935245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58235144602894917845290163 87352716904342376767935245)
  ·
    refine ⟨32757268839128391287975717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87352716904342376767935245 32757268839128391287975717)
    ·
      refine ⟨6141987907336573366495447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32757268839128391287975717 6141987907336573366495447)
      ·
        refine ⟨9212981861004860049743171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6141987907336573366495447 9212981861004860049743171)
        ·
          refine ⟨13819472791507290074614757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212981861004860049743171 13819472791507290074614757)
          ·
            refine ⟨2591151148407616888990267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13819472791507290074614757 2591151148407616888990267)
            ·
              refine ⟨3886726722611425333485401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591151148407616888990267 3886726722611425333485401)
              ·
                refine ⟨2915045041958569000114051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3886726722611425333485401 2915045041958569000114051)
                ·
                  refine ⟨4372567562937853500171077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915045041958569000114051 4372567562937853500171077)
                  ·
                    refine ⟨819856418050847531282077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4372567562937853500171077 819856418050847531282077)
                    ·
                      rfl

theorem cell22_2394997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2394997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2394997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2394997 prefixEnd_2394997 := by exact prefixLift 2394997
  have htrace : WordTrace (prefixWord ++ tailWord_2394997) baseStart_2394997 baseEnd_2394997 := by
    simpa [prefixWord, tailWord_2394997, baseEnd_2394997] using wordTrace_append hprefix tailTrace_2394997
  have hstable : (prefixWord ++ tailWord_2394997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394997).length < 2 ^ (prefixWord ++ tailWord_2394997).sum := by decide
  have hdescent : baseEnd_2394997 < baseStart_2394997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395072 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 1, 3]
def baseStart_2395072 : Nat := 118140960795 + 2395072 * 2 ^ 59
def prefixEnd_2395072 : Nat := 4983230072969 + 3 ^ 40 * 2395072 * 2
def baseEnd_2395072 : Nat := 819882092083572335656847

theorem tailTrace_2395072 : CollatzResearch.WordTrace tailWord_2395072 prefixEnd_2395072 819882092083572335656847 := by
  unfold tailWord_2395072
  simp only [CollatzResearch.WordTrace]
  refine ⟨43677726189535332288457735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58236968252713776384610313 43677726189535332288457735)
  ·
    refine ⟨65516589284302998432686603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43677726189535332288457735 65516589284302998432686603)
    ·
      refine ⟨98274883926454497649029905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65516589284302998432686603 98274883926454497649029905)
      ·
        refine ⟨73706162944840873236772429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98274883926454497649029905 73706162944840873236772429)
        ·
          refine ⟨27639811104315327463789661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73706162944840873236772429 27639811104315327463789661)
          ·
            refine ⟨10364929164118247798921123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27639811104315327463789661 10364929164118247798921123)
            ·
              refine ⟨15547393746177371698381685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10364929164118247798921123 15547393746177371698381685)
              ·
                refine ⟨1457568163704128596723283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15547393746177371698381685 1457568163704128596723283)
                ·
                  refine ⟨2186352245556192895084925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457568163704128596723283 2186352245556192895084925)
                  ·
                    refine ⟨819882092083572335656847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186352245556192895084925 819882092083572335656847)
                    ·
                      rfl

theorem cell22_2395072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_2395072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395072 prefixEnd_2395072 := by exact prefixLift 2395072
  have htrace : WordTrace (prefixWord ++ tailWord_2395072) baseStart_2395072 baseEnd_2395072 := by
    simpa [prefixWord, tailWord_2395072, baseEnd_2395072] using wordTrace_append hprefix tailTrace_2395072
  have hstable : (prefixWord ++ tailWord_2395072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395072).length < 2 ^ (prefixWord ++ tailWord_2395072).sum := by decide
  have hdescent : baseEnd_2395072 < baseStart_2395072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395078 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2395078 : Nat := 118140960795 + 2395078 * 2 ^ 59
def prefixEnd_2395078 : Nat := 4983230072969 + 3 ^ 40 * 2395078 * 2
def baseEnd_2395078 : Nat := 819884146006190320006829

theorem tailTrace_2395078 : CollatzResearch.WordTrace tailWord_2395078 prefixEnd_2395078 819884146006190320006829 := by
  unfold tailWord_2395078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729864725532778987551059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58237114144699285067755925 2729864725532778987551059)
  ·
    refine ⟨4094797088299168481326589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729864725532778987551059 4094797088299168481326589)
    ·
      refine ⟨1535548908112188180497471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4094797088299168481326589 1535548908112188180497471)
      ·
        refine ⟨2303323362168282270746207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535548908112188180497471 2303323362168282270746207)
        ·
          refine ⟨3454985043252423406119311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303323362168282270746207 3454985043252423406119311)
          ·
            refine ⟨5182477564878635109178967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454985043252423406119311 5182477564878635109178967)
            ·
              refine ⟨7773716347317952663768451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182477564878635109178967 7773716347317952663768451)
              ·
                refine ⟨11660574520976928995652677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773716347317952663768451 11660574520976928995652677)
                ·
                  refine ⟨2186357722683174186684877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11660574520976928995652677 2186357722683174186684877)
                  ·
                    refine ⟨819884146006190320006829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186357722683174186684877 819884146006190320006829)
                    ·
                      rfl

theorem cell22_2395078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2395078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395078 prefixEnd_2395078 := by exact prefixLift 2395078
  have htrace : WordTrace (prefixWord ++ tailWord_2395078) baseStart_2395078 baseEnd_2395078 := by
    simpa [prefixWord, tailWord_2395078, baseEnd_2395078] using wordTrace_append hprefix tailTrace_2395078
  have hstable : (prefixWord ++ tailWord_2395078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395078).length < 2 ^ (prefixWord ++ tailWord_2395078).sum := by decide
  have hdescent : baseEnd_2395078 < baseStart_2395078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395083 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_2395083 : Nat := 118140960795 + 2395083 * 2 ^ 59
def prefixEnd_2395083 : Nat := 4983230072969 + 3 ^ 40 * 2395083 * 2
def baseEnd_2395083 : Nat := 819885857608371973631813

theorem tailTrace_2395083 : CollatzResearch.WordTrace tailWord_2395083 prefixEnd_2395083 819885857608371973631813 := by
  unfold tailWord_2395083
  simp only [CollatzResearch.WordTrace]
  refine ⟨87355853582030813455565903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58237235721353875637043935 87355853582030813455565903)
  ·
    refine ⟨131033780373046220183348855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87355853582030813455565903 131033780373046220183348855)
    ·
      refine ⟨196550670559569330275023283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131033780373046220183348855 196550670559569330275023283)
      ·
        refine ⟨294826005839353995412534925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196550670559569330275023283 294826005839353995412534925)
        ·
          refine ⟨110559752189757748279700597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294826005839353995412534925 110559752189757748279700597)
          ·
            refine ⟨10364976767789788901221931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110559752189757748279700597 10364976767789788901221931)
            ·
              refine ⟨15547465151684683351832897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10364976767789788901221931 15547465151684683351832897)
              ·
                refine ⟨11660598863763512513874673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15547465151684683351832897 11660598863763512513874673)
                ·
                  refine ⟨8745449147822634385406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11660598863763512513874673 8745449147822634385406005)
                  ·
                    refine ⟨819885857608371973631813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8745449147822634385406005 819885857608371973631813)
                    ·
                      rfl

theorem cell22_2395083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_2395083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395083 prefixEnd_2395083 := by exact prefixLift 2395083
  have htrace : WordTrace (prefixWord ++ tailWord_2395083) baseStart_2395083 baseEnd_2395083 := by
    simpa [prefixWord, tailWord_2395083, baseEnd_2395083] using wordTrace_append hprefix tailTrace_2395083
  have hstable : (prefixWord ++ tailWord_2395083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395083).length < 2 ^ (prefixWord ++ tailWord_2395083).sum := by decide
  have hdescent : baseEnd_2395083 < baseStart_2395083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395128 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_2395128 : Nat := 118140960795 + 2395128 * 2 ^ 59
def prefixEnd_2395128 : Nat := 4983230072969 + 3 ^ 40 * 2395128 * 2
def baseEnd_2395128 : Nat := 819901262028006856256675

theorem tailTrace_2395128 : CollatzResearch.WordTrace tailWord_2395128 prefixEnd_2395128 819901262028006856256675 := by
  unfold tailWord_2395128
  simp only [CollatzResearch.WordTrace]
  refine ⟨43678747433433893070477019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58238329911245190760636025 43678747433433893070477019)
  ·
    refine ⟨65518121150150839605715529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43678747433433893070477019 65518121150150839605715529)
    ·
      refine ⟨49138590862613129704286647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65518121150150839605715529 49138590862613129704286647)
      ·
        refine ⟨73707886293919694556429971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49138590862613129704286647 73707886293919694556429971)
        ·
          refine ⟨110561829440879541834644957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73707886293919694556429971 110561829440879541834644957)
          ·
            refine ⟨41460686040329828187991859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110561829440879541834644957 41460686040329828187991859)
            ·
              refine ⟨62191029060494742281987789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41460686040329828187991859 62191029060494742281987789)
              ·
                refine ⟨23321635897685528355745421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62191029060494742281987789 23321635897685528355745421)
                ·
                  refine ⟨8745613461632073133404533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23321635897685528355745421 8745613461632073133404533)
                  ·
                    refine ⟨819901262028006856256675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8745613461632073133404533 819901262028006856256675)
                    ·
                      rfl

theorem cell22_2395128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_2395128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395128 prefixEnd_2395128 := by exact prefixLift 2395128
  have htrace : WordTrace (prefixWord ++ tailWord_2395128) baseStart_2395128 baseEnd_2395128 := by
    simpa [prefixWord, tailWord_2395128, baseEnd_2395128] using wordTrace_append hprefix tailTrace_2395128
  have hstable : (prefixWord ++ tailWord_2395128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395128).length < 2 ^ (prefixWord ++ tailWord_2395128).sum := by decide
  have hdescent : baseEnd_2395128 < baseStart_2395128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395162 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_2395162 : Nat := 118140960795 + 2395162 * 2 ^ 59
def prefixEnd_2395162 : Nat := 4983230072969 + 3 ^ 40 * 2395162 * 2
def baseEnd_2395162 : Nat := 819912900922842100906571

theorem tailTrace_2395162 : CollatzResearch.WordTrace tailWord_2395162 prefixEnd_2395162 819912900922842100906571 := by
  unfold tailWord_2395162
  simp only [CollatzResearch.WordTrace]
  refine ⟨21839683737186152486922935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58239156632496406631794493 21839683737186152486922935)
  ·
    refine ⟨32759525605779228730384403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21839683737186152486922935 32759525605779228730384403)
    ·
      refine ⟨49139288408668843095576605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32759525605779228730384403 49139288408668843095576605)
      ·
        refine ⟨18427233153250816160841227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49139288408668843095576605 18427233153250816160841227)
        ·
          refine ⟨27640849729876224241261841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18427233153250816160841227 27640849729876224241261841)
          ·
            refine ⟨20730637297407168180946381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27640849729876224241261841 20730637297407168180946381)
            ·
              refine ⟨7773988986527688067854893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20730637297407168180946381 7773988986527688067854893)
              ·
                refine ⟨2915245869947883025445585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7773988986527688067854893 2915245869947883025445585)
                ·
                  refine ⟨2186434402460912269084189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2915245869947883025445585 2186434402460912269084189)
                  ·
                    refine ⟨819912900922842100906571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186434402460912269084189 819912900922842100906571)
                    ·
                      rfl

theorem cell22_2395162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_2395162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395162 prefixEnd_2395162 := by exact prefixLift 2395162
  have htrace : WordTrace (prefixWord ++ tailWord_2395162) baseStart_2395162 baseEnd_2395162 := by
    simpa [prefixWord, tailWord_2395162, baseEnd_2395162] using wordTrace_append hprefix tailTrace_2395162
  have hstable : (prefixWord ++ tailWord_2395162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395162).length < 2 ^ (prefixWord ++ tailWord_2395162).sum := by decide
  have hdescent : baseEnd_2395162 < baseStart_2395162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395280 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_2395280 : Nat := 118140960795 + 2395280 * 2 ^ 59
def prefixEnd_2395280 : Nat := 4983230072969 + 3 ^ 40 * 2395280 * 2
def baseEnd_2395280 : Nat := 819953294734329126456209

theorem tailTrace_2395280 : CollatzResearch.WordTrace tailWord_2395280 prefixEnd_2395280 819953294734329126456209 := by
  unfold tailWord_2395280
  simp only [CollatzResearch.WordTrace]
  refine ⟨43681519381158558050243647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58242025841544744066991529 43681519381158558050243647)
  ·
    refine ⟨65522279071737837075365471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43681519381158558050243647 65522279071737837075365471)
    ·
      refine ⟨98283418607606755613048207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65522279071737837075365471 98283418607606755613048207)
      ·
        refine ⟨147425127911410133419572311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98283418607606755613048207 147425127911410133419572311)
        ·
          refine ⟨221137691867115200129358467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147425127911410133419572311 221137691867115200129358467)
          ·
            refine ⟨331706537800672800194037701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221137691867115200129358467 331706537800672800194037701)
            ·
              refine ⟨62194975837626150036382069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 331706537800672800194037701 62194975837626150036382069)
              ·
                refine ⟨5830778984777451565910819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62194975837626150036382069 5830778984777451565910819)
                ·
                  refine ⟨8746168477166177348866229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830778984777451565910819 8746168477166177348866229)
                  ·
                    refine ⟨819953294734329126456209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8746168477166177348866229 819953294734329126456209)
                    ·
                      rfl

theorem cell22_2395280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_2395280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395280 prefixEnd_2395280 := by exact prefixLift 2395280
  have htrace : WordTrace (prefixWord ++ tailWord_2395280) baseStart_2395280 baseEnd_2395280 := by
    simpa [prefixWord, tailWord_2395280, baseEnd_2395280] using wordTrace_append hprefix tailTrace_2395280
  have hstable : (prefixWord ++ tailWord_2395280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395280).length < 2 ^ (prefixWord ++ tailWord_2395280).sum := by decide
  have hdescent : baseEnd_2395280 < baseStart_2395280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395282 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_2395282 : Nat := 118140960795 + 2395282 * 2 ^ 59
def prefixEnd_2395282 : Nat := 4983230072969 + 3 ^ 40 * 2395282 * 2
def baseEnd_2395282 : Nat := 273317993125067262635401

theorem tailTrace_2395282 : CollatzResearch.WordTrace tailWord_2395282 prefixEnd_2395282 273317993125067262635401 := by
  unfold tailWord_2395282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21840777927077467610515025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58242074472206580294706733 21840777927077467610515025)
  ·
    refine ⟨16380583445308100707886269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21840777927077467610515025 16380583445308100707886269)
    ·
      refine ⟨6142718791990537765457351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16380583445308100707886269 6142718791990537765457351)
      ·
        refine ⟨9214078187985806648186027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6142718791990537765457351 9214078187985806648186027)
        ·
          refine ⟨13821117281978709972279041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9214078187985806648186027 13821117281978709972279041)
          ·
            refine ⟨10365837961484032479209281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13821117281978709972279041 10365837961484032479209281)
            ·
              refine ⟨7774378471113024359406961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10365837961484032479209281 7774378471113024359406961)
              ·
                refine ⟨5830783853334768269555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774378471113024359406961 5830783853334768269555221)
                ·
                  refine ⟨273317993125067262635401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5830783853334768269555221 273317993125067262635401)
                  ·
                    rfl

theorem cell22_2395282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_2395282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395282 prefixEnd_2395282 := by exact prefixLift 2395282
  have htrace : WordTrace (prefixWord ++ tailWord_2395282) baseStart_2395282 baseEnd_2395282 := by
    simpa [prefixWord, tailWord_2395282, baseEnd_2395282] using wordTrace_append hprefix tailTrace_2395282
  have hstable : (prefixWord ++ tailWord_2395282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395282).length < 2 ^ (prefixWord ++ tailWord_2395282).sum := by decide
  have hdescent : baseEnd_2395282 < baseStart_2395282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395297 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_2395297 : Nat := 118140960795 + 2395297 * 2 ^ 59
def prefixEnd_2395297 : Nat := 4983230072969 + 3 ^ 40 * 2395297 * 2
def baseEnd_2395297 : Nat := 819959114181746748781157

theorem tailTrace_2395297 : CollatzResearch.WordTrace tailWord_2395297 prefixEnd_2395297 819959114181746748781157 := by
  unfold tailWord_2395297
  simp only [CollatzResearch.WordTrace]
  refine ⟨87363658803255528003856145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58242439202170352002570763 87363658803255528003856145)
  ·
    refine ⟨65522744102441646002892109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87363658803255528003856145 65522744102441646002892109)
    ·
      refine ⟨24571029038415617251084541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65522744102441646002892109 24571029038415617251084541)
      ·
        refine ⟨9214135889405856469156703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24571029038415617251084541 9214135889405856469156703)
        ·
          refine ⟨13821203834108784703735055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9214135889405856469156703 13821203834108784703735055)
          ·
            refine ⟨20731805751163177055602583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13821203834108784703735055 20731805751163177055602583)
            ·
              refine ⟨31097708626744765583403875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20731805751163177055602583 31097708626744765583403875)
              ·
                refine ⟨46646562940117148375105813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31097708626744765583403875 46646562940117148375105813)
                ·
                  refine ⟨2186557637817991330083085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46646562940117148375105813 2186557637817991330083085)
                  ·
                    refine ⟨819959114181746748781157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186557637817991330083085 819959114181746748781157)
                    ·
                      rfl

theorem cell22_2395297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_2395297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395297 prefixEnd_2395297 := by exact prefixLift 2395297
  have htrace : WordTrace (prefixWord ++ tailWord_2395297) baseStart_2395297 baseEnd_2395297 := by
    simpa [prefixWord, tailWord_2395297, baseEnd_2395297] using wordTrace_append hprefix tailTrace_2395297
  have hstable : (prefixWord ++ tailWord_2395297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395297).length < 2 ^ (prefixWord ++ tailWord_2395297).sum := by decide
  have hdescent : baseEnd_2395297 < baseStart_2395297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395372 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_2395372 : Nat := 118140960795 + 2395372 * 2 ^ 59
def prefixEnd_2395372 : Nat := 4983230072969 + 3 ^ 40 * 2395372 * 2
def baseEnd_2395372 : Nat := 273328262738157184385309

theorem tailTrace_2395372 : CollatzResearch.WordTrace tailWord_2395372 prefixEnd_2395372 273328262738157184385309 := by
  unfold tailWord_2395372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43683197138991907906418185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58244262851989210541890913 43683197138991907906418185)
  ·
    refine ⟨32762397854243930929813639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43683197138991907906418185 32762397854243930929813639)
    ·
      refine ⟨49143596781365896394720459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32762397854243930929813639 49143596781365896394720459)
      ·
        refine ⟨73715395172048844592080689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49143596781365896394720459 73715395172048844592080689)
        ·
          refine ⟨55286546379036633444060517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73715395172048844592080689 55286546379036633444060517)
          ·
            refine ⟨10366227446069368770761347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55286546379036633444060517 10366227446069368770761347)
            ·
              refine ⟨15549341169104053156142021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10366227446069368770761347 15549341169104053156142021)
              ·
                refine ⟨2915501469207009966776629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15549341169104053156142021 2915501469207009966776629)
                ·
                  refine ⟨273328262738157184385309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2915501469207009966776629 273328262738157184385309)
                  ·
                    rfl

theorem cell22_2395372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_2395372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395372 prefixEnd_2395372 := by exact prefixLift 2395372
  have htrace : WordTrace (prefixWord ++ tailWord_2395372) baseStart_2395372 baseEnd_2395372 := by
    simpa [prefixWord, tailWord_2395372, baseEnd_2395372] using wordTrace_append hprefix tailTrace_2395372
  have hstable : (prefixWord ++ tailWord_2395372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395372).length < 2 ^ (prefixWord ++ tailWord_2395372).sum := by decide
  have hdescent : baseEnd_2395372 < baseStart_2395372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395434 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_2395434 : Nat := 118140960795 + 2395434 * 2 ^ 59
def prefixEnd_2395434 : Nat := 4983230072969 + 3 ^ 40 * 2395434 * 2
def baseEnd_2395434 : Nat := 273335337360508019368579

theorem tailTrace_2395434 : CollatzResearch.WordTrace tailWord_2395434 prefixEnd_2395434 273335337360508019368579 := by
  unfold tailWord_2395434
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842163900939800100398339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58245770402506133601062237 21842163900939800100398339)
  ·
    refine ⟨32763245851409700150597509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21842163900939800100398339 32763245851409700150597509)
    ·
      refine ⟨6143108597139318778237033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32763245851409700150597509 6143108597139318778237033)
      ·
        refine ⟨4607331447854489083677775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6143108597139318778237033 4607331447854489083677775)
        ·
          refine ⟨6910997171781733625516663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607331447854489083677775 6910997171781733625516663)
          ·
            refine ⟨10366495757672600438274995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6910997171781733625516663 10366495757672600438274995)
            ·
              refine ⟨15549743636508900657412493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10366495757672600438274995 15549743636508900657412493)
              ·
                refine ⟨5831153863690837746529685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15549743636508900657412493 5831153863690837746529685)
                ·
                  refine ⟨273335337360508019368579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5831153863690837746529685 273335337360508019368579)
                  ·
                    rfl

theorem cell22_2395434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_2395434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395434 prefixEnd_2395434 := by exact prefixLift 2395434
  have htrace : WordTrace (prefixWord ++ tailWord_2395434) baseStart_2395434 baseEnd_2395434 := by
    simpa [prefixWord, tailWord_2395434, baseEnd_2395434] using wordTrace_append hprefix tailTrace_2395434
  have hstable : (prefixWord ++ tailWord_2395434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395434).length < 2 ^ (prefixWord ++ tailWord_2395434).sum := by decide
  have hdescent : baseEnd_2395434 < baseStart_2395434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395453 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_2395453 : Nat := 118140960795 + 2395453 * 2 ^ 59
def prefixEnd_2395453 : Nat := 4983230072969 + 3 ^ 40 * 2395453 * 2
def baseEnd_2395453 : Nat := 820012516169814341880679

theorem tailTrace_2395453 : CollatzResearch.WordTrace tailWord_2395453 prefixEnd_2395453 820012516169814341880679 := by
  unfold tailWord_2395453
  simp only [CollatzResearch.WordTrace]
  refine ⟨87369348590690366646535013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58246232393793577764356675 87369348590690366646535013)
  ·
    refine ⟨16381752860754443746225315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87369348590690366646535013 16381752860754443746225315)
    ·
      refine ⟨24572629291131665619337973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16381752860754443746225315 24572629291131665619337973)
      ·
        refine ⟨2303683996043593651812935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24572629291131665619337973 2303683996043593651812935)
        ·
          refine ⟨3455525994065390477719403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303683996043593651812935 3455525994065390477719403)
          ·
            refine ⟨5183288991098085716579105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455525994065390477719403 5183288991098085716579105)
            ·
              refine ⟨3887466743323564287434329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5183288991098085716579105 3887466743323564287434329)
              ·
                refine ⟨2915600057492673215575747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3887466743323564287434329 2915600057492673215575747)
                ·
                  refine ⟨4373400086239009823363621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915600057492673215575747 4373400086239009823363621)
                  ·
                    refine ⟨820012516169814341880679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373400086239009823363621 820012516169814341880679)
                    ·
                      rfl

theorem cell22_2395453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_2395453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395453 prefixEnd_2395453 := by exact prefixLift 2395453
  have htrace : WordTrace (prefixWord ++ tailWord_2395453) baseStart_2395453 baseEnd_2395453 := by
    simpa [prefixWord, tailWord_2395453, baseEnd_2395453] using wordTrace_append hprefix tailTrace_2395453
  have hstable : (prefixWord ++ tailWord_2395453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395453).length < 2 ^ (prefixWord ++ tailWord_2395453).sum := by decide
  have hdescent : baseEnd_2395453 < baseStart_2395453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395485 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2395485 : Nat := 118140960795 + 2395485 * 2 ^ 59
def prefixEnd_2395485 : Nat := 4983230072969 + 3 ^ 40 * 2395485 * 2
def baseEnd_2395485 : Nat := 273341156807925641693527

theorem tailTrace_2395485 : CollatzResearch.WordTrace tailWord_2395485 prefixEnd_2395485 273341156807925641693527 := by
  unfold tailWord_2395485
  simp only [CollatzResearch.WordTrace]
  refine ⟨87370515726574436111699909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58247010484382957407799939 87370515726574436111699909)
  ·
    refine ⟨16381971698732706770943733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87370515726574436111699909 16381971698732706770943733)
    ·
      refine ⟨1535809846756191259775975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16381971698732706770943733 1535809846756191259775975)
      ·
        refine ⟨2303714770134286889663963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535809846756191259775975 2303714770134286889663963)
        ·
          refine ⟨3455572155201430334495945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303714770134286889663963 3455572155201430334495945)
          ·
            refine ⟨2591679116401072750871959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455572155201430334495945 2591679116401072750871959)
            ·
              refine ⟨3887518674601609126307939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591679116401072750871959 3887518674601609126307939)
              ·
                refine ⟨5831278011902413689461909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887518674601609126307939 5831278011902413689461909)
                ·
                  refine ⟨273341156807925641693527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5831278011902413689461909 273341156807925641693527)
                  ·
                    rfl

theorem cell22_2395485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2395485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395485 prefixEnd_2395485 := by exact prefixLift 2395485
  have htrace : WordTrace (prefixWord ++ tailWord_2395485) baseStart_2395485 baseEnd_2395485 := by
    simpa [prefixWord, tailWord_2395485, baseEnd_2395485] using wordTrace_append hprefix tailTrace_2395485
  have hstable : (prefixWord ++ tailWord_2395485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395485).length < 2 ^ (prefixWord ++ tailWord_2395485).sum := by decide
  have hdescent : baseEnd_2395485 < baseStart_2395485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395545 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 1, 3]
def baseStart_2395545 : Nat := 118140960795 + 2395545 * 2 ^ 59
def prefixEnd_2395545 : Nat := 4983230072969 + 3 ^ 40 * 2395545 * 2
def baseEnd_2395545 : Nat := 820044009649956768580397

theorem tailTrace_2395545 : CollatzResearch.WordTrace tailWord_2395545 prefixEnd_2395545 820044009649956768580397 := by
  unfold tailWord_2395545
  simp only [CollatzResearch.WordTrace]
  refine ⟨87372704106357066358884089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58248469404238044239256059 87372704106357066358884089)
  ·
    refine ⟨65529528079767799769163067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87372704106357066358884089 65529528079767799769163067)
    ·
      refine ⟨98294292119651699653744601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65529528079767799769163067 98294292119651699653744601)
      ·
        refine ⟨73720719089738774740308451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98294292119651699653744601 73720719089738774740308451)
        ·
          refine ⟨110581078634608162110462677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73720719089738774740308451 110581078634608162110462677)
          ·
            refine ⟨2591744030498628799463969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110581078634608162110462677 2591744030498628799463969)
            ·
              refine ⟨1943808022873971599597977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2591744030498628799463969 1943808022873971599597977)
              ·
                refine ⟨1457856017155478699698483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943808022873971599597977 1457856017155478699698483)
                ·
                  refine ⟨2186784025733218049547725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457856017155478699698483 2186784025733218049547725)
                  ·
                    refine ⟨820044009649956768580397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186784025733218049547725 820044009649956768580397)
                    ·
                      rfl

theorem cell22_2395545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_2395545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395545 prefixEnd_2395545 := by exact prefixLift 2395545
  have htrace : WordTrace (prefixWord ++ tailWord_2395545) baseStart_2395545 baseEnd_2395545 := by
    simpa [prefixWord, tailWord_2395545, baseEnd_2395545] using wordTrace_append hprefix tailTrace_2395545
  have hstable : (prefixWord ++ tailWord_2395545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395545).length < 2 ^ (prefixWord ++ tailWord_2395545).sum := by decide
  have hdescent : baseEnd_2395545 < baseStart_2395545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395569 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 6]
def baseStart_2395569 : Nat := 118140960795 + 2395569 * 2 ^ 59
def prefixEnd_2395569 : Nat := 4983230072969 + 3 ^ 40 * 2395569 * 2
def baseEnd_2395569 : Nat := 273350741780142901993441

theorem tailTrace_2395569 : CollatzResearch.WordTrace tailWord_2395569 prefixEnd_2395569 273350741780142901993441 := by
  unfold tailWord_2395569
  simp only [CollatzResearch.WordTrace]
  refine ⟨87373579458270118457757761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58249052972180078971838507 87373579458270118457757761)
  ·
    refine ⟨65530184593702588843318321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87373579458270118457757761 65530184593702588843318321)
    ·
      refine ⟨49147638445276941632488741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65530184593702588843318321 49147638445276941632488741)
      ·
        refine ⟨9215182208489426556091639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49147638445276941632488741 9215182208489426556091639)
        ·
          refine ⟨13822773312734139834137459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9215182208489426556091639 13822773312734139834137459)
          ·
            refine ⟨20734159969101209751206189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13822773312734139834137459 20734159969101209751206189)
            ·
              refine ⟨7775309988412953656702321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20734159969101209751206189 7775309988412953656702321)
              ·
                refine ⟨5831482491309715242526741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7775309988412953656702321 5831482491309715242526741)
                ·
                  refine ⟨273350741780142901993441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5831482491309715242526741 273350741780142901993441)
                  ·
                    rfl

theorem cell22_2395569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_2395569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395569 prefixEnd_2395569 := by exact prefixLift 2395569
  have htrace : WordTrace (prefixWord ++ tailWord_2395569) baseStart_2395569 baseEnd_2395569 := by
    simpa [prefixWord, tailWord_2395569, baseEnd_2395569] using wordTrace_append hprefix tailTrace_2395569
  have hstable : (prefixWord ++ tailWord_2395569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395569).length < 2 ^ (prefixWord ++ tailWord_2395569).sum := by decide
  have hdescent : baseEnd_2395569 < baseStart_2395569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395584 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_2395584 : Nat := 118140960795 + 2395584 * 2 ^ 59
def prefixEnd_2395584 : Nat := 4983230072969 + 3 ^ 40 * 2395584 * 2
def baseEnd_2395584 : Nat := 820057360146973666855277

theorem tailTrace_2395584 : CollatzResearch.WordTrace tailWord_2395584 prefixEnd_2395584 820057360146973666855277 := by
  unfold tailWord_2395584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43687063276607888009776903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58249417702143850679702537 43687063276607888009776903)
  ·
    refine ⟨65530594914911832014665355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43687063276607888009776903 65530594914911832014665355)
    ·
      refine ⟨98295892372367748021998033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65530594914911832014665355 98295892372367748021998033)
      ·
        refine ⟨73721919279275811016498525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98295892372367748021998033 73721919279275811016498525)
        ·
          refine ⟨27645719729728429131186947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73721919279275811016498525 27645719729728429131186947)
          ·
            refine ⟨41468579594592643696780421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27645719729728429131186947 41468579594592643696780421)
            ·
              refine ⟨7775358673986120693146329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41468579594592643696780421 7775358673986120693146329)
              ·
                refine ⟨5831519005489590519859747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7775358673986120693146329 5831519005489590519859747)
                ·
                  refine ⟨8747278508234385779789621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5831519005489590519859747 8747278508234385779789621)
                  ·
                    refine ⟨820057360146973666855277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8747278508234385779789621 820057360146973666855277)
                    ·
                      rfl

theorem cell22_2395584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_2395584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395584 prefixEnd_2395584 := by exact prefixLift 2395584
  have htrace : WordTrace (prefixWord ++ tailWord_2395584) baseStart_2395584 baseEnd_2395584 := by
    simpa [prefixWord, tailWord_2395584, baseEnd_2395584] using wordTrace_append hprefix tailTrace_2395584
  have hstable : (prefixWord ++ tailWord_2395584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395584).length < 2 ^ (prefixWord ++ tailWord_2395584).sum := by decide
  have hdescent : baseEnd_2395584 < baseStart_2395584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395588 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2395588 : Nat := 118140960795 + 2395588 * 2 ^ 59
def prefixEnd_2395588 : Nat := 4983230072969 + 3 ^ 40 * 2395588 * 2
def baseEnd_2395588 : Nat := 820058729428718989755265

theorem tailTrace_2395588 : CollatzResearch.WordTrace tailWord_2395588 prefixEnd_2395588 820058729428718989755265 := by
  unfold tailWord_2395588
  simp only [CollatzResearch.WordTrace]
  refine ⟨43687136222600642351349709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58249514963467523135132945 43687136222600642351349709)
  ·
    refine ⟨16382676083475240881756141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43687136222600642351349709 16382676083475240881756141)
    ·
      refine ⟨6143503531303215330658553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16382676083475240881756141 6143503531303215330658553)
      ·
        refine ⟨4607627648477411497993915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6143503531303215330658553 4607627648477411497993915)
        ·
          refine ⟨6911441472716117246990873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607627648477411497993915 6911441472716117246990873)
          ·
            refine ⟨5183581104537087935243155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6911441472716117246990873 5183581104537087935243155)
            ·
              refine ⟨7775371656805631902864733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5183581104537087935243155 7775371656805631902864733)
              ·
                refine ⟨2915764371302111963574275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7775371656805631902864733 2915764371302111963574275)
                ·
                  refine ⟨4373646556953167945361413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915764371302111963574275 4373646556953167945361413)
                  ·
                    refine ⟨820058729428718989755265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373646556953167945361413 820058729428718989755265)
                    ·
                      rfl

theorem cell22_2395588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2395588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395588 prefixEnd_2395588 := by exact prefixLift 2395588
  have htrace : WordTrace (prefixWord ++ tailWord_2395588) baseStart_2395588 baseEnd_2395588 := by
    simpa [prefixWord, tailWord_2395588, baseEnd_2395588] using wordTrace_append hprefix tailTrace_2395588
  have hstable : (prefixWord ++ tailWord_2395588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395588).length < 2 ^ (prefixWord ++ tailWord_2395588).sum := by decide
  have hdescent : baseEnd_2395588 < baseStart_2395588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395599 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 2, 4]
def baseStart_2395599 : Nat := 118140960795 + 2395599 * 2 ^ 59
def prefixEnd_2395599 : Nat := 4983230072969 + 3 ^ 40 * 2395599 * 2
def baseEnd_2395599 : Nat := 820062494953518627730231

theorem tailTrace_2395599 : CollatzResearch.WordTrace tailWord_2395599 prefixEnd_2395599 820062494953518627730231 := by
  unfold tailWord_2395599
  simp only [CollatzResearch.WordTrace]
  refine ⟨87374673648161433581349851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58249782432107622387566567 87374673648161433581349851)
  ·
    refine ⟨131062010472242150372024777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87374673648161433581349851 131062010472242150372024777)
    ·
      refine ⟨98296507854181612779018583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131062010472242150372024777 98296507854181612779018583)
      ·
        refine ⟨147444761781272419168527875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98296507854181612779018583 147444761781272419168527875)
        ·
          refine ⟨221167142671908628752791813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147444761781272419168527875 221167142671908628752791813)
          ·
            refine ⟨41468839250982867891148465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221167142671908628752791813 41468839250982867891148465)
            ·
              refine ⟨31101629438237150918361349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41468839250982867891148465 31101629438237150918361349)
              ·
                refine ⟨5831555519669465797192753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31101629438237150918361349 5831555519669465797192753)
                ·
                  refine ⟨4373666639752099347894565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831555519669465797192753 4373666639752099347894565)
                  ·
                    refine ⟨820062494953518627730231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373666639752099347894565 820062494953518627730231)
                    ·
                      rfl

theorem cell22_2395599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_2395599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395599 prefixEnd_2395599 := by exact prefixLift 2395599
  have htrace : WordTrace (prefixWord ++ tailWord_2395599) baseStart_2395599 baseEnd_2395599 := by
    simpa [prefixWord, tailWord_2395599, baseEnd_2395599] using wordTrace_append hprefix tailTrace_2395599
  have hstable : (prefixWord ++ tailWord_2395599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395599).length < 2 ^ (prefixWord ++ tailWord_2395599).sum := by decide
  have hdescent : baseEnd_2395599 < baseStart_2395599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395654 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2395654 : Nat := 118140960795 + 2395654 * 2 ^ 59
def prefixEnd_2395654 : Nat := 4983230072969 + 3 ^ 40 * 2395654 * 2
def baseEnd_2395654 : Nat := 273360440859172272535021

theorem tailTrace_2395654 : CollatzResearch.WordTrace tailWord_2395654 prefixEnd_2395654 273360440859172272535021 := by
  unfold tailWord_2395654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730521239467568061706313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58251119775308118649734677 2730521239467568061706313)
  ·
    refine ⟨2047890929600676046279735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2730521239467568061706313 2047890929600676046279735)
    ·
      refine ⟨3071836394401014069419603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047890929600676046279735 3071836394401014069419603)
      ·
        refine ⟨4607754591601521104129405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071836394401014069419603 4607754591601521104129405)
        ·
          refine ⟨1727907971850570414048527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4607754591601521104129405 1727907971850570414048527)
          ·
            refine ⟨2591861957775855621072791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727907971850570414048527 2591861957775855621072791)
            ·
              refine ⟨3887792936663783431609187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591861957775855621072791 3887792936663783431609187)
              ·
                refine ⟨5831689404995675147413781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887792936663783431609187 5831689404995675147413781)
                ·
                  refine ⟨273360440859172272535021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5831689404995675147413781 273360440859172272535021)
                  ·
                    rfl

theorem cell22_2395654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2395654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395654 prefixEnd_2395654 := by exact prefixLift 2395654
  have htrace : WordTrace (prefixWord ++ tailWord_2395654) baseStart_2395654 baseEnd_2395654 := by
    simpa [prefixWord, tailWord_2395654, baseEnd_2395654] using wordTrace_append hprefix tailTrace_2395654
  have hstable : (prefixWord ++ tailWord_2395654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395654).length < 2 ^ (prefixWord ++ tailWord_2395654).sum := by decide
  have hdescent : baseEnd_2395654 < baseStart_2395654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395674 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_2395674 : Nat := 118140960795 + 2395674 * 2 ^ 59
def prefixEnd_2395674 : Nat := 4983230072969 + 3 ^ 40 * 2395674 * 2
def baseEnd_2395674 : Nat := 820088168986243432105001

theorem tailTrace_2395674 : CollatzResearch.WordTrace tailWord_2395674 prefixEnd_2395674 820088168986243432105001 := by
  unfold tailWord_2395674
  simp only [CollatzResearch.WordTrace]
  refine ⟨21844352280722430347582519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58251606081926480926886717 21844352280722430347582519)
  ·
    refine ⟨32766528421083645521373779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21844352280722430347582519 32766528421083645521373779)
    ·
      refine ⟨49149792631625468282060669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32766528421083645521373779 49149792631625468282060669)
      ·
        refine ⟨18431172236859550605772751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49149792631625468282060669 18431172236859550605772751)
        ·
          refine ⟨27646758355289325908659127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18431172236859550605772751 27646758355289325908659127)
          ·
            refine ⟨41470137532933988862988691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27646758355289325908659127 41470137532933988862988691)
            ·
              refine ⟨62205206299400983294483037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41470137532933988862988691 62205206299400983294483037)
              ·
                refine ⟨23326952362275368735431139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62205206299400983294483037 23326952362275368735431139)
                ·
                  refine ⟨34990428543413053103146709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23326952362275368735431139 34990428543413053103146709)
                  ·
                    refine ⟨820088168986243432105001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34990428543413053103146709 820088168986243432105001)
                    ·
                      rfl

theorem cell22_2395674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_2395674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395674 prefixEnd_2395674 := by exact prefixLift 2395674
  have htrace : WordTrace (prefixWord ++ tailWord_2395674) baseStart_2395674 baseEnd_2395674 := by
    simpa [prefixWord, tailWord_2395674, baseEnd_2395674] using wordTrace_append hprefix tailTrace_2395674
  have hstable : (prefixWord ++ tailWord_2395674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395674).length < 2 ^ (prefixWord ++ tailWord_2395674).sum := by decide
  have hdescent : baseEnd_2395674 < baseStart_2395674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395676 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_2395676 : Nat := 118140960795 + 2395676 * 2 ^ 59
def prefixEnd_2395676 : Nat := 4983230072969 + 3 ^ 40 * 2395676 * 2
def baseEnd_2395676 : Nat := 273362951209038697851665

theorem tailTrace_2395676 : CollatzResearch.WordTrace tailWord_2395676 prefixEnd_2395676 273362951209038697851665 := by
  unfold tailWord_2395676
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688741034441237865951441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58251654712588317154601921 43688741034441237865951441)
  ·
    refine ⟨32766555775830928399463581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43688741034441237865951441 32766555775830928399463581)
    ·
      refine ⟨12287458415936598149798843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32766555775830928399463581 12287458415936598149798843)
      ·
        refine ⟨18431187623904897224698265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12287458415936598149798843 18431187623904897224698265)
        ·
          refine ⟨13823390717928672918523699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18431187623904897224698265 13823390717928672918523699)
          ·
            refine ⟨20735086076893009377785549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13823390717928672918523699 20735086076893009377785549)
            ·
              refine ⟨7775657278834878516669581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20735086076893009377785549 7775657278834878516669581)
              ·
                refine ⟨2915871479563079443751093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7775657278834878516669581 2915871479563079443751093)
                ·
                  refine ⟨273362951209038697851665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2915871479563079443751093 273362951209038697851665)
                  ·
                    rfl

theorem cell22_2395676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_2395676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395676 prefixEnd_2395676 := by exact prefixLift 2395676
  have htrace : WordTrace (prefixWord ++ tailWord_2395676) baseStart_2395676 baseEnd_2395676 := by
    simpa [prefixWord, tailWord_2395676, baseEnd_2395676] using wordTrace_append hprefix tailTrace_2395676
  have hstable : (prefixWord ++ tailWord_2395676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395676).length < 2 ^ (prefixWord ++ tailWord_2395676).sum := by decide
  have hdescent : baseEnd_2395676 < baseStart_2395676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395736 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_2395736 : Nat := 118140960795 + 2395736 * 2 ^ 59
def prefixEnd_2395736 : Nat := 4983230072969 + 3 ^ 40 * 2395736 * 2
def baseEnd_2395736 : Nat := 820109392853295937054811

theorem tailTrace_2395736 : CollatzResearch.WordTrace tailWord_2395736 prefixEnd_2395736 820109392853295937054811 := by
  unfold tailWord_2395736
  simp only [CollatzResearch.WordTrace]
  refine ⟨43689835224332552989543531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58253113632443403986058041 43689835224332552989543531)
  ·
    refine ⟨65534752836498829484315297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43689835224332552989543531 65534752836498829484315297)
    ·
      refine ⟨49151064627374122113236473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65534752836498829484315297 49151064627374122113236473)
      ·
        refine ⟨36863298470530591584927355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49151064627374122113236473 36863298470530591584927355)
        ·
          refine ⟨55294947705795887377391033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36863298470530591584927355 55294947705795887377391033)
          ·
            refine ⟨41471210779346915533043275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55294947705795887377391033 41471210779346915533043275)
            ·
              refine ⟨62206816169020373299564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41471210779346915533043275 62206816169020373299564913)
              ·
                refine ⟨46655112126765279974673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62206816169020373299564913 46655112126765279974673685)
                ·
                  refine ⟨2186958380942122498812829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46655112126765279974673685 2186958380942122498812829)
                  ·
                    refine ⟨820109392853295937054811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186958380942122498812829 820109392853295937054811)
                    ·
                      rfl

theorem cell22_2395736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_2395736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395736 prefixEnd_2395736 := by exact prefixLift 2395736
  have htrace : WordTrace (prefixWord ++ tailWord_2395736) baseStart_2395736 baseEnd_2395736 := by
    simpa [prefixWord, tailWord_2395736, baseEnd_2395736] using wordTrace_append hprefix tailTrace_2395736
  have hstable : (prefixWord ++ tailWord_2395736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395736).length < 2 ^ (prefixWord ++ tailWord_2395736).sum := by decide
  have hdescent : baseEnd_2395736 < baseStart_2395736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395757 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_2395757 : Nat := 118140960795 + 2395757 * 2 ^ 59
def prefixEnd_2395757 : Nat := 4983230072969 + 3 ^ 40 * 2395757 * 2
def baseEnd_2395757 : Nat := 820116581582458882279747

theorem tailTrace_2395757 : CollatzResearch.WordTrace tailWord_2395757 prefixEnd_2395757 820116581582458882279747 := by
  unfold tailWord_2395757
  simp only [CollatzResearch.WordTrace]
  refine ⟨87380436381589026565601525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58253624254392684377067683 87380436381589026565601525)
  ·
    refine ⟨8191915910773971240525143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87380436381589026565601525 8191915910773971240525143)
    ·
      refine ⟨12287873866160956860787715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8191915910773971240525143 12287873866160956860787715)
      ·
        refine ⟨18431810799241435291181573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12287873866160956860787715 18431810799241435291181573)
        ·
          refine ⟨3455964524857769117096545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18431810799241435291181573 3455964524857769117096545)
          ·
            refine ⟨2591973393643326837822409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455964524857769117096545 2591973393643326837822409)
            ·
              refine ⟨1943980045232495128366807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2591973393643326837822409 1943980045232495128366807)
              ·
                refine ⟨2915970067848742692550211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943980045232495128366807 2915970067848742692550211)
                ·
                  refine ⟨4373955101773114038825317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915970067848742692550211 4373955101773114038825317)
                  ·
                    refine ⟨820116581582458882279747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373955101773114038825317 820116581582458882279747)
                    ·
                      rfl

theorem cell22_2395757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_2395757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395757 prefixEnd_2395757 := by exact prefixLift 2395757
  have htrace : WordTrace (prefixWord ++ tailWord_2395757) baseStart_2395757 baseEnd_2395757 := by
    simpa [prefixWord, tailWord_2395757, baseEnd_2395757] using wordTrace_append hprefix tailTrace_2395757
  have hstable : (prefixWord ++ tailWord_2395757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395757).length < 2 ^ (prefixWord ++ tailWord_2395757).sum := by decide
  have hdescent : baseEnd_2395757 < baseStart_2395757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395826 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_2395826 : Nat := 118140960795 + 2395826 * 2 ^ 59
def prefixEnd_2395826 : Nat := 4983230072969 + 3 ^ 40 * 2395826 * 2
def baseEnd_2395826 : Nat := 820140201692565702304535

theorem tailTrace_2395826 : CollatzResearch.WordTrace tailWord_2395826 prefixEnd_2395826 820140201692565702304535 := by
  unfold tailWord_2395826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21845738254584762837465833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58255302012226034233242221 21845738254584762837465833)
  ·
    refine ⟨16384303690938572128099375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21845738254584762837465833 16384303690938572128099375)
    ·
      refine ⟨24576455536407858192149063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16384303690938572128099375 24576455536407858192149063)
      ·
        refine ⟨36864683304611787288223595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24576455536407858192149063 36864683304611787288223595)
        ·
          refine ⟨55297024956917680932335393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36864683304611787288223595 55297024956917680932335393)
          ·
            refine ⟨41472768717688260699251545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55297024956917680932335393 41472768717688260699251545)
            ·
              refine ⟨31104576538266195524438659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41472768717688260699251545 31104576538266195524438659)
              ·
                refine ⟨46656864807399293286657989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31104576538266195524438659 46656864807399293286657989)
                ·
                  refine ⟨8748162151387367491248373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46656864807399293286657989 8748162151387367491248373)
                  ·
                    refine ⟨820140201692565702304535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8748162151387367491248373 820140201692565702304535)
                    ·
                      rfl

theorem cell22_2395826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_2395826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395826 prefixEnd_2395826 := by exact prefixLift 2395826
  have htrace : WordTrace (prefixWord ++ tailWord_2395826) baseStart_2395826 baseEnd_2395826 := by
    simpa [prefixWord, tailWord_2395826, baseEnd_2395826] using wordTrace_append hprefix tailTrace_2395826
  have hstable : (prefixWord ++ tailWord_2395826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395826).length < 2 ^ (prefixWord ++ tailWord_2395826).sum := by decide
  have hdescent : baseEnd_2395826 < baseStart_2395826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395890 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_2395890 : Nat := 118140960795 + 2395890 * 2 ^ 59
def prefixEnd_2395890 : Nat := 4983230072969 + 3 ^ 40 * 2395890 * 2
def baseEnd_2395890 : Nat := 273387370066830289568113

theorem tailTrace_2395890 : CollatzResearch.WordTrace tailWord_2395890 prefixEnd_2395890 273387370066830289568113 := by
  unfold tailWord_2395890
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846321822526797570048281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58256858193404793520128749 21846321822526797570048281)
  ·
    refine ⟨16384741366895098177536211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21846321822526797570048281 16384741366895098177536211)
    ·
      refine ⟨24577112050342647266304317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16384741366895098177536211 24577112050342647266304317)
      ·
        refine ⟨9216417018878492724864119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24577112050342647266304317 9216417018878492724864119)
        ·
          refine ⟨13824625528317739087296179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9216417018878492724864119 13824625528317739087296179)
          ·
            refine ⟨20736938292476608630944269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824625528317739087296179 20736938292476608630944269)
            ·
              refine ⟨7776351859678728236604101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20736938292476608630944269 7776351859678728236604101)
              ·
                refine ⟨1458065973689761544363269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7776351859678728236604101 1458065973689761544363269)
                ·
                  refine ⟨273387370066830289568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458065973689761544363269 273387370066830289568113)
                  ·
                    rfl

theorem cell22_2395890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_2395890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395890 prefixEnd_2395890 := by exact prefixLift 2395890
  have htrace : WordTrace (prefixWord ++ tailWord_2395890) baseStart_2395890 baseEnd_2395890 := by
    simpa [prefixWord, tailWord_2395890, baseEnd_2395890] using wordTrace_append hprefix tailTrace_2395890
  have hstable : (prefixWord ++ tailWord_2395890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395890).length < 2 ^ (prefixWord ++ tailWord_2395890).sum := by decide
  have hdescent : baseEnd_2395890 < baseStart_2395890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395892 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2395892 : Nat := 118140960795 + 2395892 * 2 ^ 59
def prefixEnd_2395892 : Nat := 4983230072969 + 3 ^ 40 * 2395892 * 2
def baseEnd_2395892 : Nat := 820162794841363530154333

theorem tailTrace_2395892 : CollatzResearch.WordTrace tailWord_2395892 prefixEnd_2395892 820162794841363530154333 := by
  unfold tailWord_2395892
  simp only [CollatzResearch.WordTrace]
  refine ⟨43692680118049972310882965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58256906824066629747843953 43692680118049972310882965)
  ·
    refine ⟨2048094380533592452072639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43692680118049972310882965 2048094380533592452072639)
    ·
      refine ⟨3072141570800388678108959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048094380533592452072639 3072141570800388678108959)
      ·
        refine ⟨4608212356200583017163439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072141570800388678108959 4608212356200583017163439)
        ·
          refine ⟨6912318534300874525745159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608212356200583017163439 6912318534300874525745159)
          ·
            refine ⟨10368477801451311788617739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912318534300874525745159 10368477801451311788617739)
            ·
              refine ⟨15552716702176967682926609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10368477801451311788617739 15552716702176967682926609)
              ·
                refine ⟨11664537526632725762194957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15552716702176967682926609 11664537526632725762194957)
                ·
                  refine ⟨4374201572487272160823109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11664537526632725762194957 4374201572487272160823109)
                  ·
                    refine ⟨820162794841363530154333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374201572487272160823109 820162794841363530154333)
                    ·
                      rfl

theorem cell22_2395892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2395892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395892 prefixEnd_2395892 := by exact prefixLift 2395892
  have htrace : WordTrace (prefixWord ++ tailWord_2395892) baseStart_2395892 baseEnd_2395892 := by
    simpa [prefixWord, tailWord_2395892, baseEnd_2395892] using wordTrace_append hprefix tailTrace_2395892
  have hstable : (prefixWord ++ tailWord_2395892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395892).length < 2 ^ (prefixWord ++ tailWord_2395892).sum := by decide
  have hdescent : baseEnd_2395892 < baseStart_2395892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395901 : List Nat := [1, 4, 1, 1, 1, 1, 2, 11]
def baseStart_2395901 : Nat := 118140960795 + 2395901 * 2 ^ 59
def prefixEnd_2395901 : Nat := 4983230072969 + 3 ^ 40 * 2395901 * 2
def baseEnd_2395901 : Nat := 91129541747254500742145

theorem tailTrace_2395901 : CollatzResearch.WordTrace tailWord_2395901 prefixEnd_2395901 91129541747254500742145 := by
  unfold tailWord_2395901
  simp only [CollatzResearch.WordTrace]
  refine ⟨87385688493067339158843557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58257125662044892772562371 87385688493067339158843557)
  ·
    refine ⟨16384816592450126092283167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87385688493067339158843557 16384816592450126092283167)
    ·
      refine ⟨24577224888675189138424751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16384816592450126092283167 24577224888675189138424751)
      ·
        refine ⟨36865837333012783707637127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24577224888675189138424751 36865837333012783707637127)
        ·
          refine ⟨55298755999519175561455691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36865837333012783707637127 55298755999519175561455691)
          ·
            refine ⟨82948133999278763342183537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55298755999519175561455691 82948133999278763342183537)
            ·
              refine ⟨62211100499459072506637653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82948133999278763342183537 62211100499459072506637653)
              ·
                refine ⟨91129541747254500742145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 62211100499459072506637653 91129541747254500742145)
                ·
                  rfl

theorem cell22_2395901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 11].length) (baseStart_2395901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395901 prefixEnd_2395901 := by exact prefixLift 2395901
  have htrace : WordTrace (prefixWord ++ tailWord_2395901) baseStart_2395901 baseEnd_2395901 := by
    simpa [prefixWord, tailWord_2395901, baseEnd_2395901] using wordTrace_append hprefix tailTrace_2395901
  have hstable : (prefixWord ++ tailWord_2395901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395901).length < 2 ^ (prefixWord ++ tailWord_2395901).sum := by decide
  have hdescent : baseEnd_2395901 < baseStart_2395901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395905 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2395905 : Nat := 118140960795 + 2395905 * 2 ^ 59
def prefixEnd_2395905 : Nat := 4983230072969 + 3 ^ 40 * 2395905 * 2
def baseEnd_2395905 : Nat := 820167245007035829579293

theorem tailTrace_2395905 : CollatzResearch.WordTrace tailWord_2395905 prefixEnd_2395905 820167245007035829579293 := by
  unfold tailWord_2395905
  simp only [CollatzResearch.WordTrace]
  refine ⟨87385834385052847841989169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58257222923368565227992779 87385834385052847841989169)
  ·
    refine ⟨65539375788789635881491877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87385834385052847841989169 65539375788789635881491877)
    ·
      refine ⟨12288632960398056727779727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65539375788789635881491877 12288632960398056727779727)
      ·
        refine ⟨18432949440597085091669591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288632960398056727779727 18432949440597085091669591)
        ·
          refine ⟨27649424160895627637504387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18432949440597085091669591 27649424160895627637504387)
          ·
            refine ⟨41474136241343441456256581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27649424160895627637504387 41474136241343441456256581)
            ·
              refine ⟨7776400545251895273048109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41474136241343441456256581 7776400545251895273048109)
              ·
                refine ⟨2916150204469460727393041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7776400545251895273048109 2916150204469460727393041)
                ·
                  refine ⟨2187112653352095545544781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916150204469460727393041 2187112653352095545544781)
                  ·
                    refine ⟨820167245007035829579293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187112653352095545544781 820167245007035829579293)
                    ·
                      rfl

theorem cell22_2395905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2395905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395905 prefixEnd_2395905 := by exact prefixLift 2395905
  have htrace : WordTrace (prefixWord ++ tailWord_2395905) baseStart_2395905 baseEnd_2395905 := by
    simpa [prefixWord, tailWord_2395905, baseEnd_2395905] using wordTrace_append hprefix tailTrace_2395905
  have hstable : (prefixWord ++ tailWord_2395905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395905).length < 2 ^ (prefixWord ++ tailWord_2395905).sum := by decide
  have hdescent : baseEnd_2395905 < baseStart_2395905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395931 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_2395931 : Nat := 118140960795 + 2395931 * 2 ^ 59
def prefixEnd_2395931 : Nat := 4983230072969 + 3 ^ 40 * 2395931 * 2
def baseEnd_2395931 : Nat := 820176145338380428429213

theorem tailTrace_2395931 : CollatzResearch.WordTrace tailWord_2395931 prefixEnd_2395931 820176145338380428429213 := by
  unfold tailWord_2395931
  simp only [CollatzResearch.WordTrace]
  refine ⟨87386782682958654282435647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58257855121972436188290431 87386782682958654282435647)
  ·
    refine ⟨131080174024437981423653471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87386782682958654282435647 131080174024437981423653471)
    ·
      refine ⟨196620261036656972135480207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131080174024437981423653471 196620261036656972135480207)
      ·
        refine ⟨294930391554985458203220311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196620261036656972135480207 294930391554985458203220311)
        ·
          refine ⟨442395587332478187304830467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294930391554985458203220311 442395587332478187304830467)
          ·
            refine ⟨663593380998717280957245701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442395587332478187304830467 663593380998717280957245701)
            ·
              refine ⟨124423758937259490179483569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 663593380998717280957245701 124423758937259490179483569)
              ·
                refine ⟨93317819202944617634612677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124423758937259490179483569 93317819202944617634612677)
                ·
                  refine ⟨17497091100552115806489877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93317819202944617634612677 17497091100552115806489877)
                  ·
                    refine ⟨820176145338380428429213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17497091100552115806489877 820176145338380428429213)
                    ·
                      rfl

theorem cell22_2395931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_2395931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2395931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2395931 prefixEnd_2395931 := by exact prefixLift 2395931
  have htrace : WordTrace (prefixWord ++ tailWord_2395931) baseStart_2395931 baseEnd_2395931 := by
    simpa [prefixWord, tailWord_2395931, baseEnd_2395931] using wordTrace_append hprefix tailTrace_2395931
  have hstable : (prefixWord ++ tailWord_2395931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395931).length < 2 ^ (prefixWord ++ tailWord_2395931).sum := by decide
  have hdescent : baseEnd_2395931 < baseStart_2395931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396014 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_2396014 : Nat := 118140960795 + 2396014 * 2 ^ 59
def prefixEnd_2396014 : Nat := 4983230072969 + 3 ^ 40 * 2396014 * 2
def baseEnd_2396014 : Nat := 273401519311531959534653

theorem tailTrace_2396014 : CollatzResearch.WordTrace tailWord_2396014 prefixEnd_2396014 273401519311531959534653 := by
  unfold tailWord_2396014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10923726242707244932213387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58259873294438639638471397 10923726242707244932213387)
  ·
    refine ⟨16385589364060867398320081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10923726242707244932213387 16385589364060867398320081)
    ·
      refine ⟨12289192023045650548740061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16385589364060867398320081 12289192023045650548740061)
      ·
        refine ⟨4608447008642118955777523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12289192023045650548740061 4608447008642118955777523)
        ·
          refine ⟨6912670512963178433666285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608447008642118955777523 6912670512963178433666285)
          ·
            refine ⟨2592251442361191912624857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6912670512963178433666285 2592251442361191912624857)
            ·
              refine ⟨1944188581770893934468643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592251442361191912624857 1944188581770893934468643)
              ·
                refine ⟨2916282872656340901702965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944188581770893934468643 2916282872656340901702965)
                ·
                  refine ⟨273401519311531959534653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916282872656340901702965 273401519311531959534653)
                  ·
                    rfl

theorem cell22_2396014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_2396014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396014 prefixEnd_2396014 := by exact prefixLift 2396014
  have htrace : WordTrace (prefixWord ++ tailWord_2396014) baseStart_2396014 baseEnd_2396014 := by
    simpa [prefixWord, tailWord_2396014, baseEnd_2396014] using wordTrace_append hprefix tailTrace_2396014
  have hstable : (prefixWord ++ tailWord_2396014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396014).length < 2 ^ (prefixWord ++ tailWord_2396014).sum := by decide
  have hdescent : baseEnd_2396014 < baseStart_2396014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396055 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 2, 4]
def baseStart_2396055 : Nat := 118140960795 + 2396055 * 2 ^ 59
def prefixEnd_2396055 : Nat := 4983230072969 + 3 ^ 40 * 2396055 * 2
def baseEnd_2396055 : Nat := 820218593072485438328833

theorem tailTrace_2396055 : CollatzResearch.WordTrace tailWord_2396055 prefixEnd_2396055 820218593072485438328833 := by
  unfold tailWord_2396055
  simp only [CollatzResearch.WordTrace]
  refine ⟨87391305334509423459949619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58260870223006282306633079 87391305334509423459949619)
  ·
    refine ⟨131086958001764135189924429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87391305334509423459949619 131086958001764135189924429)
    ·
      refine ⟨49157609250661550696221661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131086958001764135189924429 49157609250661550696221661)
      ·
        refine ⟨18434103468998081511083123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49157609250661550696221661 18434103468998081511083123)
        ·
          refine ⟨27651155203497122266624685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18434103468998081511083123 27651155203497122266624685)
          ·
            refine ⟨10369183201311420849984257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27651155203497122266624685 10369183201311420849984257)
            ·
              refine ⟨7776887400983565637488193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10369183201311420849984257 7776887400983565637488193)
              ·
                refine ⟨5832665550737674228116145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7776887400983565637488193 5832665550737674228116145)
                ·
                  refine ⟨4374499163053255671087109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832665550737674228116145 4374499163053255671087109)
                  ·
                    refine ⟨820218593072485438328833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374499163053255671087109 820218593072485438328833)
                    ·
                      rfl

theorem cell22_2396055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_2396055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396055 prefixEnd_2396055 := by exact prefixLift 2396055
  have htrace : WordTrace (prefixWord ++ tailWord_2396055) baseStart_2396055 baseEnd_2396055 := by
    simpa [prefixWord, tailWord_2396055, baseEnd_2396055] using wordTrace_append hprefix tailTrace_2396055
  have hstable : (prefixWord ++ tailWord_2396055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396055).length < 2 ^ (prefixWord ++ tailWord_2396055).sum := by decide
  have hdescent : baseEnd_2396055 < baseStart_2396055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396083 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_2396083 : Nat := 118140960795 + 2396083 * 2 ^ 59
def prefixEnd_2396083 : Nat := 4983230072969 + 3 ^ 40 * 2396083 * 2
def baseEnd_2396083 : Nat := 820228178044702698628747

theorem tailTrace_2396083 : CollatzResearch.WordTrace tailWord_2396083 prefixEnd_2396083 820228178044702698628747 := by
  unfold tailWord_2396083
  simp only [CollatzResearch.WordTrace]
  refine ⟨87392326578407984241968903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58261551052271989494645935 87392326578407984241968903)
  ·
    refine ⟨131088489867611976362953355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87392326578407984241968903 131088489867611976362953355)
    ·
      refine ⟨196632734801417964544430033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131088489867611976362953355 196632734801417964544430033)
      ·
        refine ⟨147474551101063473408322525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196632734801417964544430033 147474551101063473408322525)
        ·
          refine ⟨55302956662898802528120947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147474551101063473408322525 55302956662898802528120947)
          ·
            refine ⟨82954434994348203792181421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55302956662898802528120947 82954434994348203792181421)
            ·
              refine ⟨31107913122880576422068033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82954434994348203792181421 31107913122880576422068033)
              ·
                refine ⟨23330934842160432316551025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31107913122880576422068033 23330934842160432316551025)
                ·
                  refine ⟨17498201131620324237413269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23330934842160432316551025 17498201131620324237413269)
                  ·
                    refine ⟨820228178044702698628747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17498201131620324237413269 820228178044702698628747)
                    ·
                      rfl

theorem cell22_2396083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_2396083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396083 prefixEnd_2396083 := by exact prefixLift 2396083
  have htrace : WordTrace (prefixWord ++ tailWord_2396083) baseStart_2396083 baseEnd_2396083 := by
    simpa [prefixWord, tailWord_2396083, baseEnd_2396083] using wordTrace_append hprefix tailTrace_2396083
  have hstable : (prefixWord ++ tailWord_2396083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396083).length < 2 ^ (prefixWord ++ tailWord_2396083).sum := by decide
  have hdescent : baseEnd_2396083 < baseStart_2396083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396132 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 5]
def baseStart_2396132 : Nat := 118140960795 + 2396132 * 2 ^ 59
def prefixEnd_2396132 : Nat := 4983230072969 + 3 ^ 40 * 2396132 * 2
def baseEnd_2396132 : Nat := 273414983915360968051199

theorem tailTrace_2396132 : CollatzResearch.WordTrace tailWord_2396132 prefixEnd_2396132 273414983915360968051199 := by
  unfold tailWord_2396132
  simp only [CollatzResearch.WordTrace]
  refine ⟨43697056877615232805251325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58262742503486977073668433 43697056877615232805251325)
  ·
    refine ⟨16386396329105712301969247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43697056877615232805251325 16386396329105712301969247)
    ·
      refine ⟨24579594493658568452953871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386396329105712301969247 24579594493658568452953871)
      ·
        refine ⟨36869391740487852679430807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24579594493658568452953871 36869391740487852679430807)
        ·
          refine ⟨55304087610731779019146211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36869391740487852679430807 55304087610731779019146211)
          ·
            refine ⟨82956131416097668528719317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55304087610731779019146211 82956131416097668528719317)
            ·
              refine ⟨1944284330064789106141859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82956131416097668528719317 1944284330064789106141859)
              ·
                refine ⟨2916426495097183659212789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944284330064789106141859 2916426495097183659212789)
                ·
                  refine ⟨273414983915360968051199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916426495097183659212789 273414983915360968051199)
                  ·
                    rfl

theorem cell22_2396132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_2396132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396132 prefixEnd_2396132 := by exact prefixLift 2396132
  have htrace : WordTrace (prefixWord ++ tailWord_2396132) baseStart_2396132 baseEnd_2396132 := by
    simpa [prefixWord, tailWord_2396132, baseEnd_2396132] using wordTrace_append hprefix tailTrace_2396132
  have hstable : (prefixWord ++ tailWord_2396132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396132).length < 2 ^ (prefixWord ++ tailWord_2396132).sum := by decide
  have hdescent : baseEnd_2396132 < baseStart_2396132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396196 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_2396196 : Nat := 118140960795 + 2396196 * 2 ^ 59
def prefixEnd_2396196 : Nat := 4983230072969 + 3 ^ 40 * 2396196 * 2
def baseEnd_2396196 : Nat := 820266860254008070553401

theorem tailTrace_2396196 : CollatzResearch.WordTrace tailWord_2396196 prefixEnd_2396196 820266860254008070553401 := by
  unfold tailWord_2396196
  simp only [CollatzResearch.WordTrace]
  refine ⟨43698224013499302270416221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58264298684665736360554961 43698224013499302270416221)
  ·
    refine ⟨16386834005062238351406083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43698224013499302270416221 16386834005062238351406083)
    ·
      refine ⟨24580251007593357527109125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386834005062238351406083 24580251007593357527109125)
      ·
        refine ⟨4608797063923754536332961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24580251007593357527109125 4608797063923754536332961)
        ·
          refine ⟨3456597797942815902249721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4608797063923754536332961 3456597797942815902249721)
          ·
            refine ⟨2592448348457111926687291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3456597797942815902249721 2592448348457111926687291)
            ·
              refine ⟨3888672522685667890030937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592448348457111926687291 3888672522685667890030937)
              ·
                refine ⟨2916504392014250917523203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888672522685667890030937 2916504392014250917523203)
                ·
                  refine ⟨4374756588021376376284805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916504392014250917523203 4374756588021376376284805)
                  ·
                    refine ⟨820266860254008070553401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374756588021376376284805 820266860254008070553401)
                    ·
                      rfl

theorem cell22_2396196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_2396196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396196 prefixEnd_2396196 := by exact prefixLift 2396196
  have htrace : WordTrace (prefixWord ++ tailWord_2396196) baseStart_2396196 baseEnd_2396196 := by
    simpa [prefixWord, tailWord_2396196, baseEnd_2396196] using wordTrace_append hprefix tailTrace_2396196
  have hstable : (prefixWord ++ tailWord_2396196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396196).length < 2 ^ (prefixWord ++ tailWord_2396196).sum := by decide
  have hdescent : baseEnd_2396196 < baseStart_2396196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396222 : List Nat := [4, 2, 1, 3, 2, 10]
def baseStart_2396222 : Nat := 118140960795 + 2396222 * 2 ^ 59
def prefixEnd_2396222 : Nat := 4983230072969 + 3 ^ 40 * 2396222 * 2
def baseEnd_2396222 : Nat := 10126861241794477400041

theorem tailTrace_2396222 : CollatzResearch.WordTrace tailWord_2396222 prefixEnd_2396222 10126861241794477400041 := by
  unfold tailWord_2396222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924674540613051372659865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58264930883269607320852613 10924674540613051372659865)
  ·
    refine ⟨8193505905459788529494899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10924674540613051372659865 8193505905459788529494899)
    ·
      refine ⟨12290258858189682794242349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8193505905459788529494899 12290258858189682794242349)
      ·
        refine ⟨4608847071821131047840881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12290258858189682794242349 4608847071821131047840881)
        ·
          refine ⟨3456635303865848285880661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4608847071821131047840881 3456635303865848285880661)
          ·
            refine ⟨10126861241794477400041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3456635303865848285880661 10126861241794477400041)
            ·
              rfl

theorem cell22_2396222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 10].length) (baseStart_2396222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396222 prefixEnd_2396222 := by exact prefixLift 2396222
  have htrace : WordTrace (prefixWord ++ tailWord_2396222) baseStart_2396222 baseEnd_2396222 := by
    simpa [prefixWord, tailWord_2396222, baseEnd_2396222] using wordTrace_append hprefix tailTrace_2396222
  have hstable : (prefixWord ++ tailWord_2396222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396222).length < 2 ^ (prefixWord ++ tailWord_2396222).sum := by decide
  have hdescent : baseEnd_2396222 < baseStart_2396222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396258 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2396258 : Nat := 118140960795 + 2396258 * 2 ^ 59
def prefixEnd_2396258 : Nat := 4983230072969 + 3 ^ 40 * 2396258 * 2
def baseEnd_2396258 : Nat := 820288084121060575503211

theorem tailTrace_2396258 : CollatzResearch.WordTrace tailWord_2396258 prefixEnd_2396258 820288084121060575503211 := by
  unfold tailWord_2396258
  simp only [CollatzResearch.WordTrace]
  refine ⟨21849677338193497282397357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58265806235182659419726285 21849677338193497282397357)
  ·
    refine ⟨8193629001822561480899009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21849677338193497282397357 8193629001822561480899009)
    ·
      refine ⟨6145221751366921110674257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8193629001822561480899009 6145221751366921110674257)
      ·
        refine ⟨4608916313525190833005693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6145221751366921110674257 4608916313525190833005693)
        ·
          refine ⟨1728343617571946562377135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4608916313525190833005693 1728343617571946562377135)
          ·
            refine ⟨2592515426357919843565703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728343617571946562377135 2592515426357919843565703)
            ·
              refine ⟨3888773139536879765348555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592515426357919843565703 3888773139536879765348555)
              ·
                refine ⟨5833159709305319648022833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888773139536879765348555 5833159709305319648022833)
                ·
                  refine ⟨4374869781978989736017125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5833159709305319648022833 4374869781978989736017125)
                  ·
                    refine ⟨820288084121060575503211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374869781978989736017125 820288084121060575503211)
                    ·
                      rfl

theorem cell22_2396258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2396258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396258 prefixEnd_2396258 := by exact prefixLift 2396258
  have htrace : WordTrace (prefixWord ++ tailWord_2396258) baseStart_2396258 baseEnd_2396258 := by
    simpa [prefixWord, tailWord_2396258, baseEnd_2396258] using wordTrace_append hprefix tailTrace_2396258
  have hstable : (prefixWord ++ tailWord_2396258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396258).length < 2 ^ (prefixWord ++ tailWord_2396258).sum := by decide
  have hdescent : baseEnd_2396258 < baseStart_2396258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396265 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_2396265 : Nat := 118140960795 + 2396265 * 2 ^ 59
def prefixEnd_2396265 : Nat := 4983230072969 + 3 ^ 40 * 2396265 * 2
def baseEnd_2396265 : Nat := 820290480364114890578189

theorem tailTrace_2396265 : CollatzResearch.WordTrace tailWord_2396265 prefixEnd_2396265 820290480364114890578189 := by
  unfold tailWord_2396265
  simp only [CollatzResearch.WordTrace]
  refine ⟨87398964663748629325094249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58265976442499086216729499 87398964663748629325094249)
  ·
    refine ⟨65549223497811471993820687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87398964663748629325094249 65549223497811471993820687)
    ·
      refine ⟨98323835246717207990731031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65549223497811471993820687 98323835246717207990731031)
      ·
        refine ⟨147485752870075811986096547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98323835246717207990731031 147485752870075811986096547)
        ·
          refine ⟨221228629305113717979144821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147485752870075811986096547 221228629305113717979144821)
          ·
            refine ⟨20740183997354411060544827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221228629305113717979144821 20740183997354411060544827)
            ·
              refine ⟨31110275996031616590817241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20740183997354411060544827 31110275996031616590817241)
              ·
                refine ⟨23332706997023712443112931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31110275996031616590817241 23332706997023712443112931)
                ·
                  refine ⟨34999060495535568664669397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23332706997023712443112931 34999060495535568664669397)
                  ·
                    refine ⟨820290480364114890578189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34999060495535568664669397 820290480364114890578189)
                    ·
                      rfl

theorem cell22_2396265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_2396265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396265 prefixEnd_2396265 := by exact prefixLift 2396265
  have htrace : WordTrace (prefixWord ++ tailWord_2396265) baseStart_2396265 baseEnd_2396265 := by
    simpa [prefixWord, tailWord_2396265, baseEnd_2396265] using wordTrace_append hprefix tailTrace_2396265
  have hstable : (prefixWord ++ tailWord_2396265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396265).length < 2 ^ (prefixWord ++ tailWord_2396265).sum := by decide
  have hdescent : baseEnd_2396265 < baseStart_2396265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396271 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 1, 3]
def baseStart_2396271 : Nat := 118140960795 + 2396271 * 2 ^ 59
def prefixEnd_2396271 : Nat := 4983230072969 + 3 ^ 40 * 2396271 * 2
def baseEnd_2396271 : Nat := 820292534286732874928171

theorem tailTrace_2396271 : CollatzResearch.WordTrace tailWord_2396271 prefixEnd_2396271 820292534286732874928171 := by
  unfold tailWord_2396271
  simp only [CollatzResearch.WordTrace]
  refine ⟨87399183501726892349812667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58266122334484594899875111 87399183501726892349812667)
  ·
    refine ⟨131098775252590338524719001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87399183501726892349812667 131098775252590338524719001)
    ·
      refine ⟨98324081439442753893539251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131098775252590338524719001 98324081439442753893539251)
      ·
        refine ⟨147486122159164130840308877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98324081439442753893539251 147486122159164130840308877)
        ·
          refine ⟨55307295809686549065115829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147486122159164130840308877 55307295809686549065115829)
          ·
            refine ⟨5185058982158113974854609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55307295809686549065115829 5185058982158113974854609)
            ·
              refine ⟨3888794236618585481140957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5185058982158113974854609 3888794236618585481140957)
              ·
                refine ⟨1458297838731969555427859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3888794236618585481140957 1458297838731969555427859)
                ·
                  refine ⟨2187446758097954333141789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458297838731969555427859 2187446758097954333141789)
                  ·
                    refine ⟨820292534286732874928171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187446758097954333141789 820292534286732874928171)
                    ·
                      rfl

theorem cell22_2396271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_2396271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396271 prefixEnd_2396271 := by exact prefixLift 2396271
  have htrace : WordTrace (prefixWord ++ tailWord_2396271) baseStart_2396271 baseEnd_2396271 := by
    simpa [prefixWord, tailWord_2396271, baseEnd_2396271] using wordTrace_append hprefix tailTrace_2396271
  have hstable : (prefixWord ++ tailWord_2396271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396271).length < 2 ^ (prefixWord ++ tailWord_2396271).sum := by decide
  have hdescent : baseEnd_2396271 < baseStart_2396271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396284 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 5]
def baseStart_2396284 : Nat := 118140960795 + 2396284 * 2 ^ 59
def prefixEnd_2396284 : Nat := 4983230072969 + 3 ^ 40 * 2396284 * 2
def baseEnd_2396284 : Nat := 273432328150801724784377

theorem tailTrace_2396284 : CollatzResearch.WordTrace tailWord_2396284 prefixEnd_2396284 273432328150801724784377 := by
  unfold tailWord_2396284
  simp only [CollatzResearch.WordTrace]
  refine ⟨43699828825339897785017953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58266438433786530380023937 43699828825339897785017953)
  ·
    refine ⟨32774871619004923338763465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43699828825339897785017953 32774871619004923338763465)
    ·
      refine ⟨24581153714253692504072599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32774871619004923338763465 24581153714253692504072599)
      ·
        refine ⟨36871730571380538756108899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24581153714253692504072599 36871730571380538756108899)
        ·
          refine ⟨55307595857070808134163349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36871730571380538756108899 55307595857070808134163349)
          ·
            refine ⟨2592543555800194131288907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55307595857070808134163349 2592543555800194131288907)
            ·
              refine ⟨3888815333700291196933361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592543555800194131288907 3888815333700291196933361)
              ·
                refine ⟨2916611500275218397700021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888815333700291196933361 2916611500275218397700021)
                ·
                  refine ⟨273432328150801724784377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916611500275218397700021 273432328150801724784377)
                  ·
                    rfl

theorem cell22_2396284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_2396284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396284 prefixEnd_2396284 := by exact prefixLift 2396284
  have htrace : WordTrace (prefixWord ++ tailWord_2396284) baseStart_2396284 baseEnd_2396284 := by
    simpa [prefixWord, tailWord_2396284, baseEnd_2396284] using wordTrace_append hprefix tailTrace_2396284
  have hstable : (prefixWord ++ tailWord_2396284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396284).length < 2 ^ (prefixWord ++ tailWord_2396284).sum := by decide
  have hdescent : baseEnd_2396284 < baseStart_2396284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396344 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_2396344 : Nat := 118140960795 + 2396344 * 2 ^ 59
def prefixEnd_2396344 : Nat := 4983230072969 + 3 ^ 40 * 2396344 * 2
def baseEnd_2396344 : Nat := 820317523678585017852947

theorem tailTrace_2396344 : CollatzResearch.WordTrace tailWord_2396344 prefixEnd_2396344 820317523678585017852947 := by
  unfold tailWord_2396344
  simp only [CollatzResearch.WordTrace]
  refine ⟨43700923015231212908610043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58267897353641617211480057 43700923015231212908610043)
  ·
    refine ⟨65551384522846819362915065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43700923015231212908610043 65551384522846819362915065)
    ·
      refine ⟨49163538392135114522186299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65551384522846819362915065 49163538392135114522186299)
      ·
        refine ⟨73745307588202671783279449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49163538392135114522186299 73745307588202671783279449)
        ·
          refine ⟨55308980691152003837459587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73745307588202671783279449 55308980691152003837459587)
          ·
            refine ⟨82963471036728005756189381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55308980691152003837459587 82963471036728005756189381)
            ·
              refine ⟨15555650819386501079285509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82963471036728005756189381 15555650819386501079285509)
              ·
                refine ⟨2916684528634968952366033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15555650819386501079285509 2916684528634968952366033)
                ·
                  refine ⟨2187513396476226714274525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916684528634968952366033 2187513396476226714274525)
                  ·
                    refine ⟨820317523678585017852947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187513396476226714274525 820317523678585017852947)
                    ·
                      rfl

theorem cell22_2396344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_2396344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396344 prefixEnd_2396344 := by exact prefixLift 2396344
  have htrace : WordTrace (prefixWord ++ tailWord_2396344) baseStart_2396344 baseEnd_2396344 := by
    simpa [prefixWord, tailWord_2396344, baseEnd_2396344] using wordTrace_append hprefix tailTrace_2396344
  have hstable : (prefixWord ++ tailWord_2396344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396344).length < 2 ^ (prefixWord ++ tailWord_2396344).sum := by decide
  have hdescent : baseEnd_2396344 < baseStart_2396344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396423 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 3, 3]
def baseStart_2396423 : Nat := 118140960795 + 2396423 * 2 ^ 59
def prefixEnd_2396423 : Nat := 4983230072969 + 3 ^ 40 * 2396423 * 2
def baseEnd_2396423 : Nat := 820344566993055145127705

theorem tailTrace_2396423 : CollatzResearch.WordTrace tailWord_2396423 prefixEnd_2396423 820344566993055145127705 := by
  unfold tailWord_2396423
  simp only [CollatzResearch.WordTrace]
  refine ⟨87404727397176222309345923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58269818264784148206230615 87404727397176222309345923)
  ·
    refine ⟨131107091095764333464018885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87404727397176222309345923 131107091095764333464018885)
    ·
      refine ⟨24582579580455812524503541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131107091095764333464018885 24582579580455812524503541)
      ·
        refine ⟨2304616835667732424172207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24582579580455812524503541 2304616835667732424172207)
        ·
          refine ⟨3456925253501598636258311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304616835667732424172207 3456925253501598636258311)
          ·
            refine ⟨5185387880252397954387467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456925253501598636258311 5185387880252397954387467)
            ·
              refine ⟨7778081820378596931581201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185387880252397954387467 7778081820378596931581201)
              ·
                refine ⟨5833561365283947698685901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7778081820378596931581201 5833561365283947698685901)
                ·
                  refine ⟨2187585511981480387007213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5833561365283947698685901 2187585511981480387007213)
                  ·
                    refine ⟨820344566993055145127705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187585511981480387007213 820344566993055145127705)
                    ·
                      rfl

theorem cell22_2396423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_2396423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396423 prefixEnd_2396423 := by exact prefixLift 2396423
  have htrace : WordTrace (prefixWord ++ tailWord_2396423) baseStart_2396423 baseEnd_2396423 := by
    simpa [prefixWord, tailWord_2396423, baseEnd_2396423] using wordTrace_append hprefix tailTrace_2396423
  have hstable : (prefixWord ++ tailWord_2396423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396423).length < 2 ^ (prefixWord ++ tailWord_2396423).sum := by decide
  have hdescent : baseEnd_2396423 < baseStart_2396423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396453 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 5]
def baseStart_2396453 : Nat := 118140960795 + 2396453 * 2 ^ 59
def prefixEnd_2396453 : Nat := 4983230072969 + 3 ^ 40 * 2396453 * 2
def baseEnd_2396453 : Nat := 273451612202048355625871

theorem tailTrace_2396453 : CollatzResearch.WordTrace tailWord_2396453 prefixEnd_2396453 273451612202048355625871 := by
  unfold tailWord_2396453
  simp only [CollatzResearch.WordTrace]
  refine ⟨87405821587067537432938013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58270547724711691621958675 87405821587067537432938013)
  ·
    refine ⟨32777183095150326537351755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87405821587067537432938013 32777183095150326537351755)
    ·
      refine ⟨49165774642725489806027633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32777183095150326537351755 49165774642725489806027633)
      ·
        refine ⟨36874330982044117354520725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49165774642725489806027633 36874330982044117354520725)
        ·
          refine ⟨1728484264783318000993159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36874330982044117354520725 1728484264783318000993159)
          ·
            refine ⟨2592726397174977001489739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728484264783318000993159 2592726397174977001489739)
            ·
              refine ⟨3889089595762465502234609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592726397174977001489739 3889089595762465502234609)
              ·
                refine ⟨2916817196821849126675957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3889089595762465502234609 2916817196821849126675957)
                ·
                  refine ⟨273451612202048355625871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916817196821849126675957 273451612202048355625871)
                  ·
                    rfl

theorem cell22_2396453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_2396453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396453 prefixEnd_2396453 := by exact prefixLift 2396453
  have htrace : WordTrace (prefixWord ++ tailWord_2396453) baseStart_2396453 baseEnd_2396453 := by
    simpa [prefixWord, tailWord_2396453, baseEnd_2396453] using wordTrace_append hprefix tailTrace_2396453
  have hstable : (prefixWord ++ tailWord_2396453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396453).length < 2 ^ (prefixWord ++ tailWord_2396453).sum := by decide
  have hdescent : baseEnd_2396453 < baseStart_2396453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396530 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_2396530 : Nat := 118140960795 + 2396530 * 2 ^ 59
def prefixEnd_2396530 : Nat := 4983230072969 + 3 ^ 40 * 2396530 * 2
def baseEnd_2396530 : Nat := 820381195279742532702377

theorem tailTrace_2396530 : CollatzResearch.WordTrace tailWord_2396530 prefixEnd_2396530 820381195279742532702377 := by
  unfold tailWord_2396530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21852157501947144895872761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58272420005192386388994029 21852157501947144895872761)
  ·
    refine ⟨16389118126460358671904571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21852157501947144895872761 16389118126460358671904571)
    ·
      refine ⟨24583677189690538007856857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16389118126460358671904571 24583677189690538007856857)
      ·
        refine ⟨18437757892267903505892643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24583677189690538007856857 18437757892267903505892643)
        ·
          refine ⟨27656636838401855258838965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18437757892267903505892643 27656636838401855258838965)
          ·
            refine ⟨2592809703600173930516153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27656636838401855258838965 2592809703600173930516153)
            ·
              refine ⟨1944607277700130447887115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592809703600173930516153 1944607277700130447887115)
              ·
                refine ⟨2916910916550195671830673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944607277700130447887115 2916910916550195671830673)
                ·
                  refine ⟨2187683187412646753873005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916910916550195671830673 2187683187412646753873005)
                  ·
                    refine ⟨820381195279742532702377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187683187412646753873005 820381195279742532702377)
                    ·
                      rfl

theorem cell22_2396530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_2396530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396530 prefixEnd_2396530 := by exact prefixLift 2396530
  have htrace : WordTrace (prefixWord ++ tailWord_2396530) baseStart_2396530 baseEnd_2396530 := by
    simpa [prefixWord, tailWord_2396530, baseEnd_2396530] using wordTrace_append hprefix tailTrace_2396530
  have hstable : (prefixWord ++ tailWord_2396530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396530).length < 2 ^ (prefixWord ++ tailWord_2396530).sum := by decide
  have hdescent : baseEnd_2396530 < baseStart_2396530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396566 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2396566 : Nat := 118140960795 + 2396566 * 2 ^ 59
def prefixEnd_2396566 : Nat := 4983230072969 + 3 ^ 40 * 2396566 * 2
def baseEnd_2396566 : Nat := 273464506271816812934089

theorem tailTrace_2396566 : CollatzResearch.WordTrace tailWord_2396566 prefixEnd_2396566 273464506271816812934089 := by
  unfold tailWord_2396566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5463121439728634858237597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58273295357105438487867701 5463121439728634858237597)
  ·
    refine ⟨2048670539898238071839099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5463121439728634858237597 2048670539898238071839099)
    ·
      refine ⟨3073005809847357107758649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048670539898238071839099 3073005809847357107758649)
      ·
        refine ⟨2304754357385517830818987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3073005809847357107758649 2304754357385517830818987)
        ·
          refine ⟨3457131536078276746228481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304754357385517830818987 3457131536078276746228481)
          ·
            refine ⟨2592848652058707559671361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3457131536078276746228481 2592848652058707559671361)
            ·
              refine ⟨1944636489044030669753521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592848652058707559671361 1944636489044030669753521)
              ·
                refine ⟨1458477366783023002315141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944636489044030669753521 1458477366783023002315141)
                ·
                  refine ⟨273464506271816812934089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458477366783023002315141 273464506271816812934089)
                  ·
                    rfl

theorem cell22_2396566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2396566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396566 prefixEnd_2396566 := by exact prefixLift 2396566
  have htrace : WordTrace (prefixWord ++ tailWord_2396566) baseStart_2396566 baseEnd_2396566 := by
    simpa [prefixWord, tailWord_2396566, baseEnd_2396566] using wordTrace_append hprefix tailTrace_2396566
  have hstable : (prefixWord ++ tailWord_2396566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396566).length < 2 ^ (prefixWord ++ tailWord_2396566).sum := by decide
  have hdescent : baseEnd_2396566 < baseStart_2396566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396569 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_2396569 : Nat := 118140960795 + 2396569 * 2 ^ 59
def prefixEnd_2396569 : Nat := 4983230072969 + 3 ^ 40 * 2396569 * 2
def baseEnd_2396569 : Nat := 820394545776759430977257

theorem tailTrace_2396569 : CollatzResearch.WordTrace tailWord_2396569 prefixEnd_2396569 820394545776759430977257 := by
  unfold tailWord_2396569
  simp only [CollatzResearch.WordTrace]
  refine ⟨87410052454647289244160761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58273368303098192829440507 87410052454647289244160761)
  ·
    refine ⟨65557539340985466933120571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87410052454647289244160761 65557539340985466933120571)
    ·
      refine ⟨98336309011478200399680857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65557539340985466933120571 98336309011478200399680857)
      ·
        refine ⟨73752231758608650299760643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98336309011478200399680857 73752231758608650299760643)
        ·
          refine ⟨110628347637912975449640965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73752231758608650299760643 110628347637912975449640965)
          ·
            refine ⟨20742815182108682896807681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110628347637912975449640965 20742815182108682896807681)
            ·
              refine ⟨15557111386581512172605761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20742815182108682896807681 15557111386581512172605761)
              ·
                refine ⟨11667833539936134129454321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15557111386581512172605761 11667833539936134129454321)
                ·
                  refine ⟨8750875154952100597090741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11667833539936134129454321 8750875154952100597090741)
                  ·
                    refine ⟨820394545776759430977257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8750875154952100597090741 820394545776759430977257)
                    ·
                      rfl

theorem cell22_2396569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_2396569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396569 prefixEnd_2396569 := by exact prefixLift 2396569
  have htrace : WordTrace (prefixWord ++ tailWord_2396569) baseStart_2396569 baseEnd_2396569 := by
    simpa [prefixWord, tailWord_2396569, baseEnd_2396569] using wordTrace_append hprefix tailTrace_2396569
  have hstable : (prefixWord ++ tailWord_2396569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396569).length < 2 ^ (prefixWord ++ tailWord_2396569).sum := by decide
  have hdescent : baseEnd_2396569 < baseStart_2396569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396599 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 8]
def baseStart_2396599 : Nat := 118140960795 + 2396599 * 2 ^ 59
def prefixEnd_2396599 : Nat := 4983230072969 + 3 ^ 40 * 2396599 * 2
def baseEnd_2396599 : Nat := 273468271796616450909055

theorem tailTrace_2396599 : CollatzResearch.WordTrace tailWord_2396599 prefixEnd_2396599 273468271796616450909055 := by
  unfold tailWord_2396599
  simp only [CollatzResearch.WordTrace]
  refine ⟨87411146644538604367752851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58274097763025736245168567 87411146644538604367752851)
  ·
    refine ⟨131116719966807906551629277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87411146644538604367752851 131116719966807906551629277)
    ·
      refine ⟨49168769987552964956860979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131116719966807906551629277 49168769987552964956860979)
      ·
        refine ⟨73753154981329447435291469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49168769987552964956860979 73753154981329447435291469)
        ·
          refine ⟨27657433117998542788234301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73753154981329447435291469 27657433117998542788234301)
          ·
            refine ⟨10371537419249453545587863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27657433117998542788234301 10371537419249453545587863)
            ·
              refine ⟨15557306128874180318381795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10371537419249453545587863 15557306128874180318381795)
              ·
                refine ⟨23335959193311270477572693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15557306128874180318381795 23335959193311270477572693)
                ·
                  refine ⟨273468271796616450909055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23335959193311270477572693 273468271796616450909055)
                  ·
                    rfl

theorem cell22_2396599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_2396599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396599 prefixEnd_2396599 := by exact prefixLift 2396599
  have htrace : WordTrace (prefixWord ++ tailWord_2396599) baseStart_2396599 baseEnd_2396599 := by
    simpa [prefixWord, tailWord_2396599, baseEnd_2396599] using wordTrace_append hprefix tailTrace_2396599
  have hstable : (prefixWord ++ tailWord_2396599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396599).length < 2 ^ (prefixWord ++ tailWord_2396599).sum := by decide
  have hdescent : baseEnd_2396599 < baseStart_2396599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396601 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_2396601 : Nat := 118140960795 + 2396601 * 2 ^ 59
def prefixEnd_2396601 : Nat := 4983230072969 + 3 ^ 40 * 2396601 * 2
def baseEnd_2396601 : Nat := 820405500030722014177159

theorem tailTrace_2396601 : CollatzResearch.WordTrace tailWord_2396601 prefixEnd_2396601 820405500030722014177159 := by
  unfold tailWord_2396601
  simp only [CollatzResearch.WordTrace]
  refine ⟨87411219590531358709325657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58274146393687572472883771 87411219590531358709325657)
  ·
    refine ⟨65558414692898519031994243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87411219590531358709325657 65558414692898519031994243)
    ·
      refine ⟨98337622039347778547991365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65558414692898519031994243 98337622039347778547991365)
      ·
        refine ⟨18438304132377708477748381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98337622039347778547991365 18438304132377708477748381)
        ·
          refine ⟨6914364049641640679155643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18438304132377708477748381 6914364049641640679155643)
          ·
            refine ⟨10371546074462461018733465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6914364049641640679155643 10371546074462461018733465)
            ·
              refine ⟨7778659555846845764050099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10371546074462461018733465 7778659555846845764050099)
              ·
                refine ⟨11667989333770268646075149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7778659555846845764050099 11667989333770268646075149)
                ·
                  refine ⟨4375496000163850742278181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11667989333770268646075149 4375496000163850742278181)
                  ·
                    refine ⟨820405500030722014177159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4375496000163850742278181 820405500030722014177159)
                    ·
                      rfl

theorem cell22_2396601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_2396601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396601 prefixEnd_2396601 := by exact prefixLift 2396601
  have htrace : WordTrace (prefixWord ++ tailWord_2396601) baseStart_2396601 baseEnd_2396601 := by
    simpa [prefixWord, tailWord_2396601, baseEnd_2396601] using wordTrace_append hprefix tailTrace_2396601
  have hstable : (prefixWord ++ tailWord_2396601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396601).length < 2 ^ (prefixWord ++ tailWord_2396601).sum := by decide
  have hdescent : baseEnd_2396601 < baseStart_2396601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396648 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2396648 : Nat := 118140960795 + 2396648 * 2 ^ 59
def prefixEnd_2396648 : Nat := 4983230072969 + 3 ^ 40 * 2396648 * 2
def baseEnd_2396648 : Nat := 820421589091229558252015

theorem tailTrace_2396648 : CollatzResearch.WordTrace tailWord_2396648 prefixEnd_2396648 820421589091229558252015 := by
  unfold tailWord_2396648
  simp only [CollatzResearch.WordTrace]
  refine ⟨43706466910680542868143299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58275289214240723824191065 43706466910680542868143299)
  ·
    refine ⟨65559700366020814302214949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43706466910680542868143299 65559700366020814302214949)
    ·
      refine ⟨12292443818628902681665303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65559700366020814302214949 12292443818628902681665303)
      ·
        refine ⟨18438665727943354022497955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12292443818628902681665303 18438665727943354022497955)
        ·
          refine ⟨27657998591915031033746933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18438665727943354022497955 27657998591915031033746933)
          ·
            refine ⟨2592937367992034159413775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27657998591915031033746933 2592937367992034159413775)
            ·
              refine ⟨3889406051988051239120663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592937367992034159413775 3889406051988051239120663)
              ·
                refine ⟨5834109077982076858680995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889406051988051239120663 5834109077982076858680995)
                ·
                  refine ⟨8751163616973115288021493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834109077982076858680995 8751163616973115288021493)
                  ·
                    refine ⟨820421589091229558252015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8751163616973115288021493 820421589091229558252015)
                    ·
                      rfl

theorem cell22_2396648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2396648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396648 prefixEnd_2396648 := by exact prefixLift 2396648
  have htrace : WordTrace (prefixWord ++ tailWord_2396648) baseStart_2396648 baseEnd_2396648 := by
    simpa [prefixWord, tailWord_2396648, baseEnd_2396648] using wordTrace_append hprefix tailTrace_2396648
  have hstable : (prefixWord ++ tailWord_2396648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396648).length < 2 ^ (prefixWord ++ tailWord_2396648).sum := by decide
  have hdescent : baseEnd_2396648 < baseStart_2396648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396659 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_2396659 : Nat := 118140960795 + 2396659 * 2 ^ 59
def prefixEnd_2396659 : Nat := 4983230072969 + 3 ^ 40 * 2396659 * 2
def baseEnd_2396659 : Nat := 820425354616029196226981

theorem tailTrace_2396659 : CollatzResearch.WordTrace tailWord_2396659 prefixEnd_2396659 820425354616029196226981 := by
  unfold tailWord_2396659
  simp only [CollatzResearch.WordTrace]
  refine ⟨87413335024321234614937031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58275556682880823076624687 87413335024321234614937031)
  ·
    refine ⟨131120002536481851922405547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87413335024321234614937031 131120002536481851922405547)
    ·
      refine ⟨196680003804722777883608321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131120002536481851922405547 196680003804722777883608321)
      ·
        refine ⟨147510002853542083412706241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196680003804722777883608321 147510002853542083412706241)
        ·
          refine ⟨110632502140156562559529681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147510002853542083412706241 110632502140156562559529681)
          ·
            refine ⟨82974376605117421919647261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110632502140156562559529681 82974376605117421919647261)
            ·
              refine ⟨31115391226919033219867723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82974376605117421919647261 31115391226919033219867723)
              ·
                refine ⟨46673086840378549829801585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31115391226919033219867723 46673086840378549829801585)
                ·
                  refine ⟨35004815130283912372351189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46673086840378549829801585 35004815130283912372351189)
                  ·
                    refine ⟨820425354616029196226981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35004815130283912372351189 820425354616029196226981)
                    ·
                      rfl

theorem cell22_2396659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_2396659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396659 prefixEnd_2396659 := by exact prefixLift 2396659
  have htrace : WordTrace (prefixWord ++ tailWord_2396659) baseStart_2396659 baseEnd_2396659 := by
    simpa [prefixWord, tailWord_2396659, baseEnd_2396659] using wordTrace_append hprefix tailTrace_2396659
  have hstable : (prefixWord ++ tailWord_2396659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396659).length < 2 ^ (prefixWord ++ tailWord_2396659).sum := by decide
  have hdescent : baseEnd_2396659 < baseStart_2396659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396800 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_2396800 : Nat := 118140960795 + 2396800 * 2 ^ 59
def prefixEnd_2396800 : Nat := 4983230072969 + 3 ^ 40 * 2396800 * 2
def baseEnd_2396800 : Nat := 820473621797551828451549

theorem tailTrace_2396800 : CollatzResearch.WordTrace tailWord_2396800 prefixEnd_2396800 820473621797551828451549 := by
  unfold tailWord_2396800
  simp only [CollatzResearch.WordTrace]
  refine ⟨43709238858405207847909927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58278985144540277130546569 43709238858405207847909927)
  ·
    refine ⟨65563858287607811771864891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43709238858405207847909927 65563858287607811771864891)
    ·
      refine ⟨98345787431411717657797337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65563858287607811771864891 98345787431411717657797337)
      ·
        refine ⟨73759340573558788243348003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98345787431411717657797337 73759340573558788243348003)
        ·
          refine ⟨110639010860338182365022005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73759340573558788243348003 110639010860338182365022005)
          ·
            refine ⟨10372407268156704596720813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110639010860338182365022005 10372407268156704596720813)
            ·
              refine ⟨3889652725558764223770305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10372407268156704596720813 3889652725558764223770305)
              ·
                refine ⟨2917239544169073167827729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3889652725558764223770305 2917239544169073167827729)
                ·
                  refine ⟨2187929658126804875870797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2917239544169073167827729 2187929658126804875870797)
                  ·
                    refine ⟨820473621797551828451549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187929658126804875870797 820473621797551828451549)
                    ·
                      rfl

theorem cell22_2396800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_2396800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396800 prefixEnd_2396800 := by exact prefixLift 2396800
  have htrace : WordTrace (prefixWord ++ tailWord_2396800) baseStart_2396800 baseEnd_2396800 := by
    simpa [prefixWord, tailWord_2396800, baseEnd_2396800] using wordTrace_append hprefix tailTrace_2396800
  have hstable : (prefixWord ++ tailWord_2396800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396800).length < 2 ^ (prefixWord ++ tailWord_2396800).sum := by decide
  have hdescent : baseEnd_2396800 < baseStart_2396800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396841 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 7]
def baseStart_2396841 : Nat := 118140960795 + 2396841 * 2 ^ 59
def prefixEnd_2396841 : Nat := 4983230072969 + 3 ^ 40 * 2396841 * 2
def baseEnd_2396841 : Nat := 273495885645147129392141

theorem tailTrace_2396841 : CollatzResearch.WordTrace tailWord_2396841 prefixEnd_2396841 273495885645147129392141 := by
  unfold tailWord_2396841
  simp only [CollatzResearch.WordTrace]
  refine ⟨87419973109661879698062377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58279982073107919798708251 87419973109661879698062377)
  ·
    refine ⟨65564979832246409773546783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87419973109661879698062377 65564979832246409773546783)
    ·
      refine ⟨98347469748369614660320175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65564979832246409773546783 98347469748369614660320175)
      ·
        refine ⟨147521204622554421990480263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98347469748369614660320175 147521204622554421990480263)
        ·
          refine ⟨221281806933831632985720395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147521204622554421990480263 221281806933831632985720395)
          ·
            refine ⟨331922710400747449478580593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221281806933831632985720395 331922710400747449478580593)
            ·
              refine ⟨248942032800560587108935445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331922710400747449478580593 248942032800560587108935445)
              ·
                refine ⟨11669157787526277520731349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248942032800560587108935445 11669157787526277520731349)
                ·
                  refine ⟨273495885645147129392141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11669157787526277520731349 273495885645147129392141)
                  ·
                    rfl

theorem cell22_2396841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_2396841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396841 prefixEnd_2396841 := by exact prefixLift 2396841
  have htrace : WordTrace (prefixWord ++ tailWord_2396841) baseStart_2396841 baseEnd_2396841 := by
    simpa [prefixWord, tailWord_2396841, baseEnd_2396841] using wordTrace_append hprefix tailTrace_2396841
  have hstable : (prefixWord ++ tailWord_2396841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396841).length < 2 ^ (prefixWord ++ tailWord_2396841).sum := by decide
  have hdescent : baseEnd_2396841 < baseStart_2396841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396858 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_2396858 : Nat := 118140960795 + 2396858 * 2 ^ 59
def prefixEnd_2396858 : Nat := 4983230072969 + 3 ^ 40 * 2396858 * 2
def baseEnd_2396858 : Nat := 273497825460953003500457

theorem tailTrace_2396858 : CollatzResearch.WordTrace tailWord_2396858 prefixEnd_2396858 273497825460953003500457 := by
  unfold tailWord_2396858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21855148287650072900357807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58280395433733527734287485 21855148287650072900357807)
  ·
    refine ⟨32782722431475109350536711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21855148287650072900357807 32782722431475109350536711)
    ·
      refine ⟨49174083647212664025805067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32782722431475109350536711 49174083647212664025805067)
      ·
        refine ⟨73761125470818996038707601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49174083647212664025805067 73761125470818996038707601)
        ·
          refine ⟨55320844103114247029030701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73761125470818996038707601 55320844103114247029030701)
          ·
            refine ⟨20745316538667842635886513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55320844103114247029030701 20745316538667842635886513)
            ·
              refine ⟨15558987404000881976914885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20745316538667842635886513 15558987404000881976914885)
              ·
                refine ⟨2917310138250165370671541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15558987404000881976914885 2917310138250165370671541)
                ·
                  refine ⟨273497825460953003500457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2917310138250165370671541 273497825460953003500457)
                  ·
                    rfl

theorem cell22_2396858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_2396858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396858 prefixEnd_2396858 := by exact prefixLift 2396858
  have htrace : WordTrace (prefixWord ++ tailWord_2396858) baseStart_2396858 baseEnd_2396858 := by
    simpa [prefixWord, tailWord_2396858, baseEnd_2396858] using wordTrace_append hprefix tailTrace_2396858
  have hstable : (prefixWord ++ tailWord_2396858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396858).length < 2 ^ (prefixWord ++ tailWord_2396858).sum := by decide
  have hdescent : baseEnd_2396858 < baseStart_2396858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396920 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 4]
def baseStart_2396920 : Nat := 118140960795 + 2396920 * 2 ^ 59
def prefixEnd_2396920 : Nat := 4983230072969 + 3 ^ 40 * 2396920 * 2
def baseEnd_2396920 : Nat := 273504900083303838483727

theorem tailTrace_2396920 : CollatzResearch.WordTrace tailWord_2396920 prefixEnd_2396920 273504900083303838483727 := by
  unfold tailWord_2396920
  simp only [CollatzResearch.WordTrace]
  refine ⟨43711427238187838095094107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58281902984250450793458809 43711427238187838095094107)
  ·
    refine ⟨65567140857281757142641161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43711427238187838095094107 65567140857281757142641161)
    ·
      refine ⟨49175355642961317856980871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65567140857281757142641161 49175355642961317856980871)
      ·
        refine ⟨73763033464441976785471307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49175355642961317856980871 73763033464441976785471307)
        ·
          refine ⟨110644550196662965178206961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73763033464441976785471307 110644550196662965178206961)
          ·
            refine ⟨82983412647497223883655221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110644550196662965178206961 82983412647497223883655221)
            ·
              refine ⟨7779694935702864739092677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82983412647497223883655221 7779694935702864739092677)
              ·
                refine ⟨1458692800444287138579877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7779694935702864739092677 1458692800444287138579877)
                ·
                  refine ⟨273504900083303838483727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458692800444287138579877 273504900083303838483727)
                  ·
                    rfl

theorem cell22_2396920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_2396920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396920 prefixEnd_2396920 := by exact prefixLift 2396920
  have htrace : WordTrace (prefixWord ++ tailWord_2396920) baseStart_2396920 baseEnd_2396920 := by
    simpa [prefixWord, tailWord_2396920, baseEnd_2396920] using wordTrace_append hprefix tailTrace_2396920
  have hstable : (prefixWord ++ tailWord_2396920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396920).length < 2 ^ (prefixWord ++ tailWord_2396920).sum := by decide
  have hdescent : baseEnd_2396920 < baseStart_2396920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396933 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_2396933 : Nat := 118140960795 + 2396933 * 2 ^ 59
def prefixEnd_2396933 : Nat := 4983230072969 + 3 ^ 40 * 2396933 * 2
def baseEnd_2396933 : Nat := 820519150415583814876141

theorem tailTrace_2396933 : CollatzResearch.WordTrace tailWord_2396933 prefixEnd_2396933 820519150415583814876141 := by
  unfold tailWord_2396933
  simp only [CollatzResearch.WordTrace]
  refine ⟨87423328625328579410411453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58282219083552386273607635 87423328625328579410411453)
  ·
    refine ⟨32783748234498217278904295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87423328625328579410411453 32783748234498217278904295)
    ·
      refine ⟨49175622351747325918356443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32783748234498217278904295 49175622351747325918356443)
      ·
        refine ⟨73763433527620988877534665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49175622351747325918356443 73763433527620988877534665)
        ·
          refine ⟨55322575145715741658150999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73763433527620988877534665 55322575145715741658150999)
          ·
            refine ⟨82983862718573612487226499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55322575145715741658150999 82983862718573612487226499)
            ·
              refine ⟨124475794077860418730839749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82983862718573612487226499 124475794077860418730839749)
              ·
                refine ⟨23339211389598828512032453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124475794077860418730839749 23339211389598828512032453)
                ·
                  refine ⟨4376102135549780346006085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23339211389598828512032453 4376102135549780346006085)
                  ·
                    refine ⟨820519150415583814876141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4376102135549780346006085 820519150415583814876141)
                    ·
                      rfl

theorem cell22_2396933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_2396933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396933 prefixEnd_2396933 := by exact prefixLift 2396933
  have htrace : WordTrace (prefixWord ++ tailWord_2396933) baseStart_2396933 baseEnd_2396933 := by
    simpa [prefixWord, tailWord_2396933, baseEnd_2396933] using wordTrace_append hprefix tailTrace_2396933
  have hstable : (prefixWord ++ tailWord_2396933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396933).length < 2 ^ (prefixWord ++ tailWord_2396933).sum := by decide
  have hdescent : baseEnd_2396933 < baseStart_2396933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396935 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2396935 : Nat := 118140960795 + 2396935 * 2 ^ 59
def prefixEnd_2396935 : Nat := 4983230072969 + 3 ^ 40 * 2396935 * 2
def baseEnd_2396935 : Nat := 820519835056456476326135

theorem tailTrace_2396935 : CollatzResearch.WordTrace tailWord_2396935 prefixEnd_2396935 820519835056456476326135 := by
  unfold tailWord_2396935
  simp only [CollatzResearch.WordTrace]
  refine ⟨87423401571321333751984259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58282267714214222501322839 87423401571321333751984259)
  ·
    refine ⟨131135102356982000627976389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87423401571321333751984259 131135102356982000627976389)
    ·
      refine ⟨24587831691934125117745573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131135102356982000627976389 24587831691934125117745573)
      ·
        refine ⟨4610218442237648459577295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24587831691934125117745573 4610218442237648459577295)
        ·
          refine ⟨6915327663356472689365943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610218442237648459577295 6915327663356472689365943)
          ·
            refine ⟨10372991495034709034048915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915327663356472689365943 10372991495034709034048915)
            ·
              refine ⟨15559487242552063551073373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10372991495034709034048915 15559487242552063551073373)
              ·
                refine ⟨5834807715957023831652515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15559487242552063551073373 5834807715957023831652515)
                ·
                  refine ⟨8752211573935535747478773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834807715957023831652515 8752211573935535747478773)
                  ·
                    refine ⟨820519835056456476326135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8752211573935535747478773 820519835056456476326135)
                    ·
                      rfl

theorem cell22_2396935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2396935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2396935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2396935 prefixEnd_2396935 := by exact prefixLift 2396935
  have htrace : WordTrace (prefixWord ++ tailWord_2396935) baseStart_2396935 baseEnd_2396935 := by
    simpa [prefixWord, tailWord_2396935, baseEnd_2396935] using wordTrace_append hprefix tailTrace_2396935
  have hstable : (prefixWord ++ tailWord_2396935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396935).length < 2 ^ (prefixWord ++ tailWord_2396935).sum := by decide
  have hdescent : baseEnd_2396935 < baseStart_2396935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397008 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_2397008 : Nat := 118140960795 + 2397008 * 2 ^ 59
def prefixEnd_2397008 : Nat := 4983230072969 + 3 ^ 40 * 2397008 * 2
def baseEnd_2397008 : Nat := 820544824448308619250911

theorem tailTrace_2397008 : CollatzResearch.WordTrace tailWord_2397008 prefixEnd_2397008 820544824448308619250911 := by
  unfold tailWord_2397008
  simp only [CollatzResearch.WordTrace]
  refine ⟨43713032050028433609695839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58284042733371244812927785 43713032050028433609695839)
  ·
    refine ⟨65569548075042650414543759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43713032050028433609695839 65569548075042650414543759)
    ·
      refine ⟨98354322112563975621815639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65569548075042650414543759 98354322112563975621815639)
      ·
        refine ⟨147531483168845963432723459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98354322112563975621815639 147531483168845963432723459)
        ·
          refine ⟨221297224753268945149085189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147531483168845963432723459 221297224753268945149085189)
          ·
            refine ⟨41493229641237927215453473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221297224753268945149085189 41493229641237927215453473)
            ·
              refine ⟨31119922230928445411590105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41493229641237927215453473 31119922230928445411590105)
              ·
                refine ⟨23339941673196334058692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31119922230928445411590105 23339941673196334058692579)
                ·
                  refine ⟨35009912509794501088038869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23339941673196334058692579 35009912509794501088038869)
                  ·
                    refine ⟨820544824448308619250911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35009912509794501088038869 820544824448308619250911)
                    ·
                      rfl

theorem cell22_2397008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_2397008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397008 prefixEnd_2397008 := by exact prefixLift 2397008
  have htrace : WordTrace (prefixWord ++ tailWord_2397008) baseStart_2397008 baseEnd_2397008 := by
    simpa [prefixWord, tailWord_2397008, baseEnd_2397008] using wordTrace_append hprefix tailTrace_2397008
  have hstable : (prefixWord ++ tailWord_2397008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397008).length < 2 ^ (prefixWord ++ tailWord_2397008).sum := by decide
  have hdescent : baseEnd_2397008 < baseStart_2397008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397031 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2397031 : Nat := 118140960795 + 2397031 * 2 ^ 59
def prefixEnd_2397031 : Nat := 4983230072969 + 3 ^ 40 * 2397031 * 2
def baseEnd_2397031 : Nat := 820552697818344225925841

theorem tailTrace_2397031 : CollatzResearch.WordTrace tailWord_2397031 prefixEnd_2397031 820552697818344225925841 := by
  unfold tailWord_2397031
  simp only [CollatzResearch.WordTrace]
  refine ⟨87426902978973542147478947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58284601985982361431652631 87426902978973542147478947)
  ·
    refine ⟨131140354468460313221218421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87426902978973542147478947 131140354468460313221218421)
    ·
      refine ⟨12294408231418154364489227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131140354468460313221218421 12294408231418154364489227)
      ·
        refine ⟨18441612347127231546733841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12294408231418154364489227 18441612347127231546733841)
        ·
          refine ⟨13831209260345423660050381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18441612347127231546733841 13831209260345423660050381)
          ·
            refine ⟨5186703472629533872518893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13831209260345423660050381 5186703472629533872518893)
            ·
              refine ⟨1945013802236075202194585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5186703472629533872518893 1945013802236075202194585)
              ·
                refine ⟨1458760351677056401645939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945013802236075202194585 1458760351677056401645939)
                ·
                  refine ⟨2188140527515584602468909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458760351677056401645939 2188140527515584602468909)
                  ·
                    refine ⟨820552697818344225925841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2188140527515584602468909 820552697818344225925841)
                    ·
                      rfl

theorem cell22_2397031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2397031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397031 prefixEnd_2397031 := by exact prefixLift 2397031
  have htrace : WordTrace (prefixWord ++ tailWord_2397031) baseStart_2397031 baseEnd_2397031 := by
    simpa [prefixWord, tailWord_2397031, baseEnd_2397031] using wordTrace_append hprefix tailTrace_2397031
  have hstable : (prefixWord ++ tailWord_2397031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397031).length < 2 ^ (prefixWord ++ tailWord_2397031).sum := by decide
  have hdescent : baseEnd_2397031 < baseStart_2397031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397089 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 4]
def baseStart_2397089 : Nat := 118140960795 + 2397089 * 2 ^ 59
def prefixEnd_2397089 : Nat := 4983230072969 + 3 ^ 40 * 2397089 * 2
def baseEnd_2397089 : Nat := 273524184134550469325221

theorem tailTrace_2397089 : CollatzResearch.WordTrace tailWord_2397089 prefixEnd_2397089 273524184134550469325221 := by
  unfold tailWord_2397089
  simp only [CollatzResearch.WordTrace]
  refine ⟨87429018412763418053090321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58286012275175612035393547 87429018412763418053090321)
  ·
    refine ⟨65571763809572563539817741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87429018412763418053090321 65571763809572563539817741)
    ·
      refine ⟨24589411428589711327431653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65571763809572563539817741 24589411428589711327431653)
      ·
        refine ⟨4610514642860570873893435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24589411428589711327431653 4610514642860570873893435)
        ·
          refine ⟨6915771964290856310840153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610514642860570873893435 6915771964290856310840153)
          ·
            refine ⟨5186828973218142233130115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6915771964290856310840153 5186828973218142233130115)
            ·
              refine ⟨7780243459827213349695173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186828973218142233130115 7780243459827213349695173)
              ·
                refine ⟨1458795648717602503067845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7780243459827213349695173 1458795648717602503067845)
                ·
                  refine ⟨273524184134550469325221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458795648717602503067845 273524184134550469325221)
                  ·
                    rfl

theorem cell22_2397089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_2397089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397089 prefixEnd_2397089 := by exact prefixLift 2397089
  have htrace : WordTrace (prefixWord ++ tailWord_2397089) baseStart_2397089 baseEnd_2397089 := by
    simpa [prefixWord, tailWord_2397089, baseEnd_2397089] using wordTrace_append hprefix tailTrace_2397089
  have hstable : (prefixWord ++ tailWord_2397089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397089).length < 2 ^ (prefixWord ++ tailWord_2397089).sum := by decide
  have hdescent : baseEnd_2397089 < baseStart_2397089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397132 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_2397132 : Nat := 118140960795 + 2397132 * 2 ^ 59
def prefixEnd_2397132 : Nat := 4983230072969 + 3 ^ 40 * 2397132 * 2
def baseEnd_2397132 : Nat := 820587272182413629150531

theorem tailTrace_2397132 : CollatzResearch.WordTrace tailWord_2397132 prefixEnd_2397132 820587272182413629150531 := by
  unfold tailWord_2397132
  simp only [CollatzResearch.WordTrace]
  refine ⟨43715293375803818198452825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58287057834405090931270433 43715293375803818198452825)
  ·
    refine ⟨32786470031852863648839619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43715293375803818198452825 32786470031852863648839619)
    ·
      refine ⟨49179705047779295473259429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32786470031852863648839619 49179705047779295473259429)
      ·
        refine ⟨9221194696458617901236143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49179705047779295473259429 9221194696458617901236143)
        ·
          refine ⟨13831792044687926851854215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9221194696458617901236143 13831792044687926851854215)
          ·
            refine ⟨20747688067031890277781323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13831792044687926851854215 20747688067031890277781323)
            ·
              refine ⟨31121532100547835416671985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20747688067031890277781323 31121532100547835416671985)
              ·
                refine ⟨23341149075410876562503989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31121532100547835416671985 23341149075410876562503989)
                ·
                  refine ⟨2188232725819769677734749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23341149075410876562503989 2188232725819769677734749)
                  ·
                    refine ⟨820587272182413629150531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2188232725819769677734749 820587272182413629150531)
                    ·
                      rfl

theorem cell22_2397132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_2397132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397132 prefixEnd_2397132 := by exact prefixLift 2397132
  have htrace : WordTrace (prefixWord ++ tailWord_2397132) baseStart_2397132 baseEnd_2397132 := by
    simpa [prefixWord, tailWord_2397132, baseEnd_2397132] using wordTrace_append hprefix tailTrace_2397132
  have hstable : (prefixWord ++ tailWord_2397132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397132).length < 2 ^ (prefixWord ++ tailWord_2397132).sum := by decide
  have hdescent : baseEnd_2397132 < baseStart_2397132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397149 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2397149 : Nat := 118140960795 + 2397149 * 2 ^ 59
def prefixEnd_2397149 : Nat := 4983230072969 + 3 ^ 40 * 2397149 * 2
def baseEnd_2397149 : Nat := 820593091629831251475479

theorem tailTrace_2397149 : CollatzResearch.WordTrace tailWord_2397149 prefixEnd_2397149 820593091629831251475479 := by
  unfold tailWord_2397149
  simp only [CollatzResearch.WordTrace]
  refine ⟨87431206792546048300274501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58287471195030698866849667 87431206792546048300274501)
  ·
    refine ⟨16393351273602384056301469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87431206792546048300274501 16393351273602384056301469)
    ·
      refine ⟨6147506727600894021113051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16393351273602384056301469 6147506727600894021113051)
      ·
        refine ⟨9221260091401341031669577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147506727600894021113051 9221260091401341031669577)
        ·
          refine ⟨6915945068551005773752183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9221260091401341031669577 6915945068551005773752183)
          ·
            refine ⟨10373917602826508660628275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915945068551005773752183 10373917602826508660628275)
            ·
              refine ⟨15560876404239762990942413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10373917602826508660628275 15560876404239762990942413)
              ·
                refine ⟨5835328651589911121603405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15560876404239762990942413 5835328651589911121603405)
                ·
                  refine ⟨2188248244346216670601277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5835328651589911121603405 2188248244346216670601277)
                  ·
                    refine ⟨820593091629831251475479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2188248244346216670601277 820593091629831251475479)
                    ·
                      rfl

theorem cell22_2397149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2397149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397149 prefixEnd_2397149 := by exact prefixLift 2397149
  have htrace : WordTrace (prefixWord ++ tailWord_2397149) baseStart_2397149 baseEnd_2397149 := by
    simpa [prefixWord, tailWord_2397149, baseEnd_2397149] using wordTrace_append hprefix tailTrace_2397149
  have hstable : (prefixWord ++ tailWord_2397149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397149).length < 2 ^ (prefixWord ++ tailWord_2397149).sum := by decide
  have hdescent : baseEnd_2397149 < baseStart_2397149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397213 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2397213 : Nat := 118140960795 + 2397213 * 2 ^ 59
def prefixEnd_2397213 : Nat := 4983230072969 + 3 ^ 40 * 2397213 * 2
def baseEnd_2397213 : Nat := 273538333379252139291761

theorem tailTrace_2397213 : CollatzResearch.WordTrace tailWord_2397213 prefixEnd_2397213 273538333379252139291761 := by
  unfold tailWord_2397213
  simp only [CollatzResearch.WordTrace]
  refine ⟨87433541064314187230604293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58289027376209458153736195 87433541064314187230604293)
  ·
    refine ⟨16393788949558910105738305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87433541064314187230604293 16393788949558910105738305)
    ·
      refine ⟨12295341712169182579303729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16393788949558910105738305 12295341712169182579303729)
      ·
        refine ⟨9221506284126886934477797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12295341712169182579303729 9221506284126886934477797)
        ·
          refine ⟨1729032428273791300214587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9221506284126886934477797 1729032428273791300214587)
          ·
            refine ⟨2593548642410686950321881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729032428273791300214587 2593548642410686950321881)
            ·
              refine ⟨1945161481808015212741411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2593548642410686950321881 1945161481808015212741411)
              ·
                refine ⟨2917742222712022819112117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945161481808015212741411 2917742222712022819112117)
                ·
                  refine ⟨273538333379252139291761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2917742222712022819112117 273538333379252139291761)
                  ·
                    rfl

theorem cell22_2397213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2397213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397213 prefixEnd_2397213 := by exact prefixLift 2397213
  have htrace : WordTrace (prefixWord ++ tailWord_2397213) baseStart_2397213 baseEnd_2397213 := by
    simpa [prefixWord, tailWord_2397213, baseEnd_2397213] using wordTrace_append hprefix tailTrace_2397213
  have hstable : (prefixWord ++ tailWord_2397213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397213).length < 2 ^ (prefixWord ++ tailWord_2397213).sum := by decide
  have hdescent : baseEnd_2397213 < baseStart_2397213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397288 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_2397288 : Nat := 118140960795 + 2397288 * 2 ^ 59
def prefixEnd_2397288 : Nat := 4983230072969 + 3 ^ 40 * 2397288 * 2
def baseEnd_2397288 : Nat := 820640674170481222250053

theorem tailTrace_2397288 : CollatzResearch.WordTrace tailWord_2397288 prefixEnd_2397288 820640674170481222250053 := by
  unfold tailWord_2397288
  simp only [CollatzResearch.WordTrace]
  refine ⟨43718138269521237519792259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58290851026028316693056345 43718138269521237519792259)
  ·
    refine ⟨65577207404281856279688389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43718138269521237519792259 65577207404281856279688389)
    ·
      refine ⟨12295726388302848052441573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65577207404281856279688389 12295726388302848052441573)
      ·
        refine ⟨2305448697806784009832795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12295726388302848052441573 2305448697806784009832795)
        ·
          refine ⟨3458173046710176014749193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305448697806784009832795 3458173046710176014749193)
          ·
            refine ⟨2593629785032632011061895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458173046710176014749193 2593629785032632011061895)
            ·
              refine ⟨3890444677548948016592843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593629785032632011061895 3890444677548948016592843)
              ·
                refine ⟨5835667016323422024889265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890444677548948016592843 5835667016323422024889265)
                ·
                  refine ⟨4376750262242566518666949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5835667016323422024889265 4376750262242566518666949)
                  ·
                    refine ⟨820640674170481222250053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4376750262242566518666949 820640674170481222250053)
                    ·
                      rfl

theorem cell22_2397288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_2397288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397288 prefixEnd_2397288 := by exact prefixLift 2397288
  have htrace : WordTrace (prefixWord ++ tailWord_2397288) baseStart_2397288 baseEnd_2397288 := by
    simpa [prefixWord, tailWord_2397288, baseEnd_2397288] using wordTrace_append hprefix tailTrace_2397288
  have hstable : (prefixWord ++ tailWord_2397288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397288).length < 2 ^ (prefixWord ++ tailWord_2397288).sum := by decide
  have hdescent : baseEnd_2397288 < baseStart_2397288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397312 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_2397312 : Nat := 118140960795 + 2397312 * 2 ^ 59
def prefixEnd_2397312 : Nat := 4983230072969 + 3 ^ 40 * 2397312 * 2
def baseEnd_2397312 : Nat := 820648889860953159649979

theorem tailTrace_2397312 : CollatzResearch.WordTrace tailWord_2397312 prefixEnd_2397312 820648889860953159649979 := by
  unfold tailWord_2397312
  simp only [CollatzResearch.WordTrace]
  refine ⟨43718575945477763569229095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58291434593970351425638793 43718575945477763569229095)
  ·
    refine ⟨65577863918216645353843643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43718575945477763569229095 65577863918216645353843643)
    ·
      refine ⟨98366795877324968030765465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65577863918216645353843643 98366795877324968030765465)
      ·
        refine ⟨73775096907993726023074099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98366795877324968030765465 73775096907993726023074099)
        ·
          refine ⟨110662645361990589034611149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73775096907993726023074099 110662645361990589034611149)
          ·
            refine ⟨41498492010746470887979181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110662645361990589034611149 41498492010746470887979181)
            ·
              refine ⟨15561934504029926582992193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41498492010746470887979181 15561934504029926582992193)
              ·
                refine ⟨11671450878022444937244145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15561934504029926582992193 11671450878022444937244145)
                ·
                  refine ⟨8753588158516833702933109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11671450878022444937244145 8753588158516833702933109)
                  ·
                    refine ⟨820648889860953159649979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8753588158516833702933109 820648889860953159649979)
                    ·
                      rfl

theorem cell22_2397312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_2397312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397312 prefixEnd_2397312 := by exact prefixLift 2397312
  have htrace : WordTrace (prefixWord ++ tailWord_2397312) baseStart_2397312 baseEnd_2397312 := by
    simpa [prefixWord, tailWord_2397312, baseEnd_2397312] using wordTrace_append hprefix tailTrace_2397312
  have hstable : (prefixWord ++ tailWord_2397312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397312).length < 2 ^ (prefixWord ++ tailWord_2397312).sum := by decide
  have hdescent : baseEnd_2397312 < baseStart_2397312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397361 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_2397361 : Nat := 118140960795 + 2397361 * 2 ^ 59
def prefixEnd_2397361 : Nat := 4983230072969 + 3 ^ 40 * 2397361 * 2
def baseEnd_2397361 : Nat := 820665663562333365174829

theorem tailTrace_2397361 : CollatzResearch.WordTrace tailWord_2397361 prefixEnd_2397361 820665663562333365174829 := by
  unfold tailWord_2397361
  simp only [CollatzResearch.WordTrace]
  refine ⟨87438939067778008506991937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58292626045185339004661291 87438939067778008506991937)
  ·
    refine ⟨65579204300833506380243953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87438939067778008506991937 65579204300833506380243953)
    ·
      refine ⟨49184403225625129785182965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65579204300833506380243953 49184403225625129785182965)
      ·
        refine ⟨4611037802402355917360903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49184403225625129785182965 4611037802402355917360903)
        ·
          refine ⟨6916556703603533876041355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611037802402355917360903 6916556703603533876041355)
          ·
            refine ⟨10374835055405300814062033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916556703603533876041355 10374835055405300814062033)
            ·
              refine ⟨7781126291553975610546525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10374835055405300814062033 7781126291553975610546525)
              ·
                refine ⟨2917922359332740853954947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7781126291553975610546525 2917922359332740853954947)
                ·
                  refine ⟨4376883538999111280932421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917922359332740853954947 4376883538999111280932421)
                  ·
                    refine ⟨820665663562333365174829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4376883538999111280932421 820665663562333365174829)
                    ·
                      rfl

theorem cell22_2397361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_2397361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397361 prefixEnd_2397361 := by exact prefixLift 2397361
  have htrace : WordTrace (prefixWord ++ tailWord_2397361) baseStart_2397361 baseEnd_2397361 := by
    simpa [prefixWord, tailWord_2397361, baseEnd_2397361] using wordTrace_append hprefix tailTrace_2397361
  have hstable : (prefixWord ++ tailWord_2397361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397361).length < 2 ^ (prefixWord ++ tailWord_2397361).sum := by decide
  have hdescent : baseEnd_2397361 < baseStart_2397361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397376 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 6]
def baseStart_2397376 : Nat := 118140960795 + 2397376 * 2 ^ 59
def prefixEnd_2397376 : Nat := 4983230072969 + 3 ^ 40 * 2397376 * 2
def baseEnd_2397376 : Nat := 273556932789626108683261

theorem tailTrace_2397376 : CollatzResearch.WordTrace tailWord_2397376 prefixEnd_2397376 273556932789626108683261 := by
  unfold tailWord_2397376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43719743081361833034393991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58292990775149110712525321 43719743081361833034393991)
  ·
    refine ⟨65579614622042749551590987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43719743081361833034393991 65579614622042749551590987)
    ·
      refine ⟨98369421933064124327386481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65579614622042749551590987 98369421933064124327386481)
      ·
        refine ⟨73777066449798093245539861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98369421933064124327386481 73777066449798093245539861)
        ·
          refine ⟨3458299989834285620884681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73777066449798093245539861 3458299989834285620884681)
          ·
            refine ⟨2593724992375714215663511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458299989834285620884681 2593724992375714215663511)
            ·
              refine ⟨3890587488563571323495267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593724992375714215663511 3890587488563571323495267)
              ·
                refine ⟨5835881232845356985242901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890587488563571323495267 5835881232845356985242901)
                ·
                  refine ⟨273556932789626108683261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5835881232845356985242901 273556932789626108683261)
                  ·
                    rfl

theorem cell22_2397376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_2397376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397376 prefixEnd_2397376 := by exact prefixLift 2397376
  have htrace : WordTrace (prefixWord ++ tailWord_2397376) baseStart_2397376 baseEnd_2397376 := by
    simpa [prefixWord, tailWord_2397376, baseEnd_2397376] using wordTrace_append hprefix tailTrace_2397376
  have hstable : (prefixWord ++ tailWord_2397376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397376).length < 2 ^ (prefixWord ++ tailWord_2397376).sum := by decide
  have hdescent : baseEnd_2397376 < baseStart_2397376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397417 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_2397417 : Nat := 118140960795 + 2397417 * 2 ^ 59
def prefixEnd_2397417 : Nat := 4983230072969 + 3 ^ 40 * 2397417 * 2
def baseEnd_2397417 : Nat := 820684833506767885774657

theorem tailTrace_2397417 : CollatzResearch.WordTrace tailWord_2397417 prefixEnd_2397417 820684833506767885774657 := by
  unfold tailWord_2397417
  simp only [CollatzResearch.WordTrace]
  refine ⟨87440981555575130071030505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58293987703716753380687003 87440981555575130071030505)
  ·
    refine ⟨65580736166681347553272879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87440981555575130071030505 65580736166681347553272879)
    ·
      refine ⟨98371104250022021329909319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65580736166681347553272879 98371104250022021329909319)
      ·
        refine ⟨147556656375033031994863979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98371104250022021329909319 147556656375033031994863979)
        ·
          refine ⟨221334984562549547992295969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147556656375033031994863979 221334984562549547992295969)
          ·
            refine ⟨166001238421912160994221977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221334984562549547992295969 166001238421912160994221977)
            ·
              refine ⟨124500928816434120745666483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166001238421912160994221977 124500928816434120745666483)
              ·
                refine ⟨186751393224651181118499725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124500928816434120745666483 186751393224651181118499725)
                ·
                  refine ⟨70031772459244192919437397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186751393224651181118499725 70031772459244192919437397)
                  ·
                    refine ⟨820684833506767885774657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70031772459244192919437397 820684833506767885774657)
                    ·
                      rfl

theorem cell22_2397417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_2397417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397417 prefixEnd_2397417 := by exact prefixLift 2397417
  have htrace : WordTrace (prefixWord ++ tailWord_2397417) baseStart_2397417 baseEnd_2397417 := by
    simpa [prefixWord, tailWord_2397417, baseEnd_2397417] using wordTrace_append hprefix tailTrace_2397417
  have hstable : (prefixWord ++ tailWord_2397417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397417).length < 2 ^ (prefixWord ++ tailWord_2397417).sum := by decide
  have hdescent : baseEnd_2397417 < baseStart_2397417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397449 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 5]
def baseStart_2397449 : Nat := 118140960795 + 2397449 * 2 ^ 59
def prefixEnd_2397449 : Nat := 4983230072969 + 3 ^ 40 * 2397449 * 2
def baseEnd_2397449 : Nat := 273565262586910156324853

theorem tailTrace_2397449 : CollatzResearch.WordTrace tailWord_2397449 prefixEnd_2397449 273565262586910156324853 := by
  unfold tailWord_2397449
  simp only [CollatzResearch.WordTrace]
  refine ⟨87442148691459199536195401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58294765794306133024130267 87442148691459199536195401)
  ·
    refine ⟨65581611518594399652146551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87442148691459199536195401 65581611518594399652146551)
    ·
      refine ⟨98372417277891599478219827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65581611518594399652146551 98372417277891599478219827)
      ·
        refine ⟨147558625916837399217329741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98372417277891599478219827 147558625916837399217329741)
        ·
          refine ⟨55334484718814024706498653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147558625916837399217329741 55334484718814024706498653)
          ·
            refine ⟨20750431769555259264936995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55334484718814024706498653 20750431769555259264936995)
            ·
              refine ⟨31125647654332888897405493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20750431769555259264936995 31125647654332888897405493)
              ·
                refine ⟨2918029467593708334131765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31125647654332888897405493 2918029467593708334131765)
                ·
                  refine ⟨273565262586910156324853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918029467593708334131765 273565262586910156324853)
                  ·
                    rfl

theorem cell22_2397449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_2397449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397449 prefixEnd_2397449 := by exact prefixLift 2397449
  have htrace : WordTrace (prefixWord ++ tailWord_2397449) baseStart_2397449 baseEnd_2397449 := by
    simpa [prefixWord, tailWord_2397449, baseEnd_2397449] using wordTrace_append hprefix tailTrace_2397449
  have hstable : (prefixWord ++ tailWord_2397449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397449).length < 2 ^ (prefixWord ++ tailWord_2397449).sum := by decide
  have hdescent : baseEnd_2397449 < baseStart_2397449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397539 : List Nat := [1, 1, 1, 5, 2, 2, 10]
def baseStart_2397539 : Nat := 118140960795 + 2397539 * 2 ^ 59
def prefixEnd_2397539 : Nat := 4983230072969 + 3 ^ 40 * 2397539 * 2
def baseEnd_2397539 : Nat := 30397281355555564230529

theorem tailTrace_2397539 : CollatzResearch.WordTrace tailWord_2397539 prefixEnd_2397539 30397281355555564230529 := by
  unfold tailWord_2397539
  simp only [CollatzResearch.WordTrace]
  refine ⟨87445431261133144906971671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58296954174088763271314447 87445431261133144906971671)
  ·
    refine ⟨131168146891699717360457507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87445431261133144906971671 131168146891699717360457507)
    ·
      refine ⟨196752220337549576040686261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131168146891699717360457507 196752220337549576040686261)
      ·
        refine ⟨18445520656645272753814337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196752220337549576040686261 18445520656645272753814337)
        ·
          refine ⟨13834140492483954565360753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18445520656645272753814337 13834140492483954565360753)
          ·
            refine ⟨10375605369362965924020565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13834140492483954565360753 10375605369362965924020565)
            ·
              refine ⟨30397281355555564230529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10375605369362965924020565 30397281355555564230529)
              ·
                rfl

theorem cell22_2397539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 10].length) (baseStart_2397539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397539 prefixEnd_2397539 := by exact prefixLift 2397539
  have htrace : WordTrace (prefixWord ++ tailWord_2397539) baseStart_2397539 baseEnd_2397539 := by
    simpa [prefixWord, tailWord_2397539, baseEnd_2397539] using wordTrace_append hprefix tailTrace_2397539
  have hstable : (prefixWord ++ tailWord_2397539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397539).length < 2 ^ (prefixWord ++ tailWord_2397539).sum := by decide
  have hdescent : baseEnd_2397539 < baseStart_2397539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397541 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2397541 : Nat := 118140960795 + 2397541 * 2 ^ 59
def prefixEnd_2397541 : Nat := 4983230072969 + 3 ^ 40 * 2397541 * 2
def baseEnd_2397541 : Nat := 820727281240872895674277

theorem tailTrace_2397541 : CollatzResearch.WordTrace tailWord_2397541 prefixEnd_2397541 820727281240872895674277 := by
  unfold tailWord_2397541
  simp only [CollatzResearch.WordTrace]
  refine ⟨87445504207125899248544477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58297002804750599499029651 87445504207125899248544477)
  ·
    refine ⟨32792064077672212218204179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87445504207125899248544477 32792064077672212218204179)
    ·
      refine ⟨49188096116508318327306269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32792064077672212218204179 49188096116508318327306269)
      ·
        refine ⟨18445536043690619372739851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49188096116508318327306269 18445536043690619372739851)
        ·
          refine ⟨27668304065535929059109777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18445536043690619372739851 27668304065535929059109777)
          ·
            refine ⟨20751228049151946794332333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27668304065535929059109777 20751228049151946794332333)
            ·
              refine ⟨7781710518431980047874625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20751228049151946794332333 7781710518431980047874625)
              ·
                refine ⟨5836282888823985035905969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7781710518431980047874625 5836282888823985035905969)
                ·
                  refine ⟨4377212166617988776929477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5836282888823985035905969 4377212166617988776929477)
                  ·
                    refine ⟨820727281240872895674277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377212166617988776929477 820727281240872895674277)
                    ·
                      rfl

theorem cell22_2397541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2397541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397541 prefixEnd_2397541 := by exact prefixLift 2397541
  have htrace : WordTrace (prefixWord ++ tailWord_2397541) baseStart_2397541 baseEnd_2397541 := by
    simpa [prefixWord, tailWord_2397541, baseEnd_2397541] using wordTrace_append hprefix tailTrace_2397541
  have hstable : (prefixWord ++ tailWord_2397541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397541).length < 2 ^ (prefixWord ++ tailWord_2397541).sum := by decide
  have hdescent : baseEnd_2397541 < baseStart_2397541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397652 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2397652 : Nat := 118140960795 + 2397652 * 2 ^ 59
def prefixEnd_2397652 : Nat := 4983230072969 + 3 ^ 40 * 2397652 * 2
def baseEnd_2397652 : Nat := 273588426269768535382979

theorem tailTrace_2397652 : CollatzResearch.WordTrace tailWord_2397652 prefixEnd_2397652 273588426269768535382979 := by
  unfold tailWord_2397652
  simp only [CollatzResearch.WordTrace]
  refine ⟨43724776354861882602917605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58299701806482510137223473 43724776354861882602917605)
  ·
    refine ⟨8198395566536602988047051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43724776354861882602917605 8198395566536602988047051)
    ·
      refine ⟨12297593349804904482070577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8198395566536602988047051 12297593349804904482070577)
      ·
        refine ⟨9223195012353678361552933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12297593349804904482070577 9223195012353678361552933)
        ·
          refine ⟨1729349064816314692791175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9223195012353678361552933 1729349064816314692791175)
          ·
            refine ⟨2594023597224472039186763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729349064816314692791175 2594023597224472039186763)
            ·
              refine ⟨3891035395836708058780145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594023597224472039186763 3891035395836708058780145)
              ·
                refine ⟨2918276546877531044085109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3891035395836708058780145 2918276546877531044085109)
                ·
                  refine ⟨273588426269768535382979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918276546877531044085109 273588426269768535382979)
                  ·
                    rfl

theorem cell22_2397652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2397652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397652 prefixEnd_2397652 := by exact prefixLift 2397652
  have htrace : WordTrace (prefixWord ++ tailWord_2397652) baseStart_2397652 baseEnd_2397652 := by
    simpa [prefixWord, tailWord_2397652, baseEnd_2397652] using wordTrace_append hprefix tailTrace_2397652
  have hstable : (prefixWord ++ tailWord_2397652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397652).length < 2 ^ (prefixWord ++ tailWord_2397652).sum := by decide
  have hdescent : baseEnd_2397652 < baseStart_2397652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397663 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 4]
def baseStart_2397663 : Nat := 118140960795 + 2397663 * 2 ^ 59
def prefixEnd_2397663 : Nat := 4983230072969 + 3 ^ 40 * 2397663 * 2
def baseEnd_2397663 : Nat := 273589681444701748041301

theorem tailTrace_2397663 : CollatzResearch.WordTrace tailWord_2397663 prefixEnd_2397663 273589681444701748041301 := by
  unfold tailWord_2397663
  simp only [CollatzResearch.WordTrace]
  refine ⟨87449953912683914084485643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58299969275122609389657095 87449953912683914084485643)
  ·
    refine ⟨131174930869025871126728465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87449953912683914084485643 131174930869025871126728465)
    ·
      refine ⟨98381198151769403345046349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131174930869025871126728465 98381198151769403345046349)
      ·
        refine ⟨36892949306913526254392381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98381198151769403345046349 36892949306913526254392381)
        ·
          refine ⟨13834855990092572345397143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36892949306913526254392381 13834855990092572345397143)
          ·
            refine ⟨20752283985138858518095715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13834855990092572345397143 20752283985138858518095715)
            ·
              refine ⟨31128425977708287777143573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20752283985138858518095715 31128425977708287777143573)
              ·
                refine ⟨1459144967705075989553605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31128425977708287777143573 1459144967705075989553605)
                ·
                  refine ⟨273589681444701748041301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459144967705075989553605 273589681444701748041301)
                  ·
                    rfl

theorem cell22_2397663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 4].length) (baseStart_2397663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397663 prefixEnd_2397663 := by exact prefixLift 2397663
  have htrace : WordTrace (prefixWord ++ tailWord_2397663) baseStart_2397663 baseEnd_2397663 := by
    simpa [prefixWord, tailWord_2397663, baseEnd_2397663] using wordTrace_append hprefix tailTrace_2397663
  have hstable : (prefixWord ++ tailWord_2397663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397663).length < 2 ^ (prefixWord ++ tailWord_2397663).sum := by decide
  have hdescent : baseEnd_2397663 < baseStart_2397663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397676 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_2397676 : Nat := 118140960795 + 2397676 * 2 ^ 59
def prefixEnd_2397676 : Nat := 4983230072969 + 3 ^ 40 * 2397676 * 2
def baseEnd_2397676 : Nat := 820773494499777543548863

theorem tailTrace_2397676 : CollatzResearch.WordTrace tailWord_2397676 prefixEnd_2397676 820773494499777543548863 := by
  unfold tailWord_2397676
  simp only [CollatzResearch.WordTrace]
  refine ⟨43725214030818408652354441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58300285374424544869805921 43725214030818408652354441)
  ·
    refine ⟨32793910523113806489265831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43725214030818408652354441 32793910523113806489265831)
    ·
      refine ⟨49190865784670709733898747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32793910523113806489265831 49190865784670709733898747)
      ·
        refine ⟨73786298677006064600848121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49190865784670709733898747 73786298677006064600848121)
        ·
          refine ⟨55339724007754548450636091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73786298677006064600848121 55339724007754548450636091)
          ·
            refine ⟨83009586011631822675954137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55339724007754548450636091 83009586011631822675954137)
            ·
              refine ⟨62257189508723867006965603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83009586011631822675954137 62257189508723867006965603)
              ·
                refine ⟨93385784263085800510448405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62257189508723867006965603 93385784263085800510448405)
                ·
                  refine ⟨4377458637332146898927269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93385784263085800510448405 4377458637332146898927269)
                  ·
                    refine ⟨820773494499777543548863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377458637332146898927269 820773494499777543548863)
                    ·
                      rfl

theorem cell22_2397676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_2397676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397676 prefixEnd_2397676 := by exact prefixLift 2397676
  have htrace : WordTrace (prefixWord ++ tailWord_2397676) baseStart_2397676 baseEnd_2397676 := by
    simpa [prefixWord, tailWord_2397676, baseEnd_2397676] using wordTrace_append hprefix tailTrace_2397676
  have hstable : (prefixWord ++ tailWord_2397676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397676).length < 2 ^ (prefixWord ++ tailWord_2397676).sum := by decide
  have hdescent : baseEnd_2397676 < baseStart_2397676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397697 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 4]
def baseStart_2397697 : Nat := 118140960795 + 2397697 * 2 ^ 59
def prefixEnd_2397697 : Nat := 4983230072969 + 3 ^ 40 * 2397697 * 2
def baseEnd_2397697 : Nat := 273593561076313496257933

theorem tailTrace_2397697 : CollatzResearch.WordTrace tailWord_2397697 prefixEnd_2397697 273593561076313496257933 := by
  unfold tailWord_2397697
  simp only [CollatzResearch.WordTrace]
  refine ⟨87451193994560737891223345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58300795996373825260815563 87451193994560737891223345)
  ·
    refine ⟨65588395495920553418417509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87451193994560737891223345 65588395495920553418417509)
    ·
      refine ⟨12297824155485103765953283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65588395495920553418417509 12297824155485103765953283)
      ·
        refine ⟨18446736233227655648929925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12297824155485103765953283 18446736233227655648929925)
        ·
          refine ⟨3458763043730185434174361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18446736233227655648929925 3458763043730185434174361)
          ·
            refine ⟨2594072282797639075630771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458763043730185434174361 2594072282797639075630771)
            ·
              refine ⟨3891108424196458613446157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594072282797639075630771 3891108424196458613446157)
              ·
                refine ⟨1459165659073671980042309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3891108424196458613446157 1459165659073671980042309)
                ·
                  refine ⟨273593561076313496257933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459165659073671980042309 273593561076313496257933)
                  ·
                    rfl

theorem cell22_2397697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_2397697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397697 prefixEnd_2397697 := by exact prefixLift 2397697
  have htrace : WordTrace (prefixWord ++ tailWord_2397697) baseStart_2397697 baseEnd_2397697 := by
    simpa [prefixWord, tailWord_2397697, baseEnd_2397697] using wordTrace_append hprefix tailTrace_2397697
  have hstable : (prefixWord ++ tailWord_2397697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397697).length < 2 ^ (prefixWord ++ tailWord_2397697).sum := by decide
  have hdescent : baseEnd_2397697 < baseStart_2397697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397708 : List Nat := [2, 2, 1, 2, 5, 2, 8]
def baseStart_2397708 : Nat := 118140960795 + 2397708 * 2 ^ 59
def prefixEnd_2397708 : Nat := 4983230072969 + 3 ^ 40 * 2397708 * 2
def baseEnd_2397708 : Nat := 30399424027916300990695

theorem tailTrace_2397708 : CollatzResearch.WordTrace tailWord_2397708 prefixEnd_2397708 30399424027916300990695 := by
  unfold tailWord_2397708
  simp only [CollatzResearch.WordTrace]
  refine ⟨43725797598760443384936889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58301063465013924513249185 43725797598760443384936889)
  ·
    refine ⟨32794348199070332538702667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43725797598760443384936889 32794348199070332538702667)
    ·
      refine ⟨49191522298605498808054001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32794348199070332538702667 49191522298605498808054001)
      ·
        refine ⟨36893641723954124106040501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49191522298605498808054001 36893641723954124106040501)
        ·
          refine ⟨3458778911620699134941297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36893641723954124106040501 3458778911620699134941297)
          ·
            refine ⟨2594084183715524351205973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458778911620699134941297 2594084183715524351205973)
            ·
              refine ⟨30399424027916300990695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2594084183715524351205973 30399424027916300990695)
              ·
                rfl

theorem cell22_2397708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 8].length) (baseStart_2397708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397708 prefixEnd_2397708 := by exact prefixLift 2397708
  have htrace : WordTrace (prefixWord ++ tailWord_2397708) baseStart_2397708 baseEnd_2397708 := by
    simpa [prefixWord, tailWord_2397708, baseEnd_2397708] using wordTrace_append hprefix tailTrace_2397708
  have hstable : (prefixWord ++ tailWord_2397708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397708).length < 2 ^ (prefixWord ++ tailWord_2397708).sum := by decide
  have hdescent : baseEnd_2397708 < baseStart_2397708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397710 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2397710 : Nat := 118140960795 + 2397710 * 2 ^ 59
def prefixEnd_2397710 : Nat := 4983230072969 + 3 ^ 40 * 2397710 * 2
def baseEnd_2397710 : Nat := 820785133394612788198759

theorem tailTrace_2397710 : CollatzResearch.WordTrace tailWord_2397710 prefixEnd_2397710 820785133394612788198759 := by
  unfold tailWord_2397710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931458517939205138930823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58301112095675760740964389 10931458517939205138930823)
  ·
    refine ⟨16397187776908807708396235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931458517939205138930823 16397187776908807708396235)
    ·
      refine ⟨24595781665363211562594353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16397187776908807708396235 24595781665363211562594353)
      ·
        refine ⟨18446836249022408671945765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24595781665363211562594353 18446836249022408671945765)
        ·
          refine ⟨3458781796691701625989831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18446836249022408671945765 3458781796691701625989831)
          ·
            refine ⟨5188172695037552438984747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458781796691701625989831 5188172695037552438984747)
            ·
              refine ⟨7782259042556328658477121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188172695037552438984747 7782259042556328658477121)
              ·
                refine ⟨5836694281917246493857841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7782259042556328658477121 5836694281917246493857841)
                ·
                  refine ⟨4377520711437934870393381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5836694281917246493857841 4377520711437934870393381)
                  ·
                    refine ⟨820785133394612788198759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377520711437934870393381 820785133394612788198759)
                    ·
                      rfl

theorem cell22_2397710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2397710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397710 prefixEnd_2397710 := by exact prefixLift 2397710
  have htrace : WordTrace (prefixWord ++ tailWord_2397710) baseStart_2397710 baseEnd_2397710 := by
    simpa [prefixWord, tailWord_2397710, baseEnd_2397710] using wordTrace_append hprefix tailTrace_2397710
  have hstable : (prefixWord ++ tailWord_2397710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397710).length < 2 ^ (prefixWord ++ tailWord_2397710).sum := by decide
  have hdescent : baseEnd_2397710 < baseStart_2397710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397783 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 3, 4]
def baseStart_2397783 : Nat := 118140960795 + 2397783 * 2 ^ 59
def prefixEnd_2397783 : Nat := 4983230072969 + 3 ^ 40 * 2397783 * 2
def baseEnd_2397783 : Nat := 820810122786464931123535

theorem tailTrace_2397783 : CollatzResearch.WordTrace tailWord_2397783 prefixEnd_2397783 820810122786464931123535 := by
  unfold tailWord_2397783
  simp only [CollatzResearch.WordTrace]
  refine ⟨87454330672249174578854003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58302887114832783052569335 87454330672249174578854003)
  ·
    refine ⟨131181496008373761868281005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87454330672249174578854003 131181496008373761868281005)
    ·
      refine ⟨49193061003140160700605377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131181496008373761868281005 49193061003140160700605377)
      ·
        refine ⟨36894795752355120525454033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49193061003140160700605377 36894795752355120525454033)
        ·
          refine ⟨27671096814266340394090525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36894795752355120525454033 27671096814266340394090525)
          ·
            refine ⟨10376661305349877647783947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27671096814266340394090525 10376661305349877647783947)
            ·
              refine ⟨15564991958024816471675921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10376661305349877647783947 15564991958024816471675921)
              ·
                refine ⟨11673743968518612353756941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15564991958024816471675921 11673743968518612353756941)
                ·
                  refine ⟨4377653988194479632658853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11673743968518612353756941 4377653988194479632658853)
                  ·
                    refine ⟨820810122786464931123535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377653988194479632658853 820810122786464931123535)
                    ·
                      rfl

theorem cell22_2397783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_2397783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397783 prefixEnd_2397783 := by exact prefixLift 2397783
  have htrace : WordTrace (prefixWord ++ tailWord_2397783) baseStart_2397783 baseEnd_2397783 := by
    simpa [prefixWord, tailWord_2397783, baseEnd_2397783] using wordTrace_append hprefix tailTrace_2397783
  have hstable : (prefixWord ++ tailWord_2397783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397783).length < 2 ^ (prefixWord ++ tailWord_2397783).sum := by decide
  have hdescent : baseEnd_2397783 < baseStart_2397783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397800 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2397800 : Nat := 118140960795 + 2397800 * 2 ^ 59
def prefixEnd_2397800 : Nat := 4983230072969 + 3 ^ 40 * 2397800 * 2
def baseEnd_2397800 : Nat := 820815942233882553448483

theorem tailTrace_2397800 : CollatzResearch.WordTrace tailWord_2397800 prefixEnd_2397800 820815942233882553448483 := by
  unfold tailWord_2397800
  simp only [CollatzResearch.WordTrace]
  refine ⟨43727475356593793241111427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58303300475458390988148569 43727475356593793241111427)
  ·
    refine ⟨65591213034890689861667141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43727475356593793241111427 65591213034890689861667141)
    ·
      refine ⟨12298352444042004349062589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65591213034890689861667141 12298352444042004349062589)
      ·
        refine ⟨4611882166515751630898471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12298352444042004349062589 4611882166515751630898471)
        ·
          refine ⟨6917823249773627446347707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611882166515751630898471 6917823249773627446347707)
          ·
            refine ⟨10376734874660441169521561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6917823249773627446347707 10376734874660441169521561)
            ·
              refine ⟨7782551155995330877141171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10376734874660441169521561 7782551155995330877141171)
              ·
                refine ⟨11673826733992996315711757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782551155995330877141171 11673826733992996315711757)
                ·
                  refine ⟨4377685025247373618391909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11673826733992996315711757 4377685025247373618391909)
                  ·
                    refine ⟨820815942233882553448483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377685025247373618391909 820815942233882553448483)
                    ·
                      rfl

theorem cell22_2397800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2397800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397800 prefixEnd_2397800 := by exact prefixLift 2397800
  have htrace : WordTrace (prefixWord ++ tailWord_2397800) baseStart_2397800 baseEnd_2397800 := by
    simpa [prefixWord, tailWord_2397800, baseEnd_2397800] using wordTrace_append hprefix tailTrace_2397800
  have hstable : (prefixWord ++ tailWord_2397800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397800).length < 2 ^ (prefixWord ++ tailWord_2397800).sum := by decide
  have hdescent : baseEnd_2397800 < baseStart_2397800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397832 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 6]
def baseStart_2397832 : Nat := 118140960795 + 2397832 * 2 ^ 59
def prefixEnd_2397832 : Nat := 4983230072969 + 3 ^ 40 * 2397832 * 2
def baseEnd_2397832 : Nat := 273608965495948378882795

theorem tailTrace_2397832 : CollatzResearch.WordTrace tailWord_2397832 prefixEnd_2397832 273608965495948378882795 := by
  unfold tailWord_2397832
  simp only [CollatzResearch.WordTrace]
  refine ⟨43728058924535827973693875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58304078566047770631591833 43728058924535827973693875)
  ·
    refine ⟨65592088386803741960540813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43728058924535827973693875 65592088386803741960540813)
    ·
      refine ⟨24597033145051403235202805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65592088386803741960540813 24597033145051403235202805)
      ·
        refine ⟨2305971857348569053300263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24597033145051403235202805 2305971857348569053300263)
        ·
          refine ⟨3458957786022853579950395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305971857348569053300263 3458957786022853579950395)
          ·
            refine ⟨5188436679034280369925593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458957786022853579950395 5188436679034280369925593)
            ·
              refine ⟨3891327509275710277444195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5188436679034280369925593 3891327509275710277444195)
              ·
                refine ⟨5836991263913565416166293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891327509275710277444195 5836991263913565416166293)
                ·
                  refine ⟨273608965495948378882795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5836991263913565416166293 273608965495948378882795)
                  ·
                    rfl

theorem cell22_2397832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_2397832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397832 prefixEnd_2397832 := by exact prefixLift 2397832
  have htrace : WordTrace (prefixWord ++ tailWord_2397832) baseStart_2397832 baseEnd_2397832 := by
    simpa [prefixWord, tailWord_2397832, baseEnd_2397832] using wordTrace_append hprefix tailTrace_2397832
  have hstable : (prefixWord ++ tailWord_2397832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397832).length < 2 ^ (prefixWord ++ tailWord_2397832).sum := by decide
  have hdescent : baseEnd_2397832 < baseStart_2397832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397860 : List Nat := [2, 3, 1, 2, 2, 2, 4, 6]
def baseStart_2397860 : Nat := 118140960795 + 2397860 * 2 ^ 59
def prefixEnd_2397860 : Nat := 4983230072969 + 3 ^ 40 * 2397860 * 2
def baseEnd_2397860 : Nat := 91204053495562488549811

theorem tailTrace_2397860 : CollatzResearch.WordTrace tailWord_2397860 prefixEnd_2397860 91204053495562488549811 := by
  unfold tailWord_2397860
  simp only [CollatzResearch.WordTrace]
  refine ⟨43728569546485108364703517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58304759395313477819604689 43728569546485108364703517)
  ·
    refine ⟨16398213579931915636763819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43728569546485108364703517 16398213579931915636763819)
    ·
      refine ⟨24597320369897873455145729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16398213579931915636763819 24597320369897873455145729)
      ·
        refine ⟨18447990277423405091359297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24597320369897873455145729 18447990277423405091359297)
        ·
          refine ⟨13835992708067553818519473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18447990277423405091359297 13835992708067553818519473)
          ·
            refine ⟨10376994531050665363889605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13835992708067553818519473 10376994531050665363889605)
            ·
              refine ⟨1945686474571999755729301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10376994531050665363889605 1945686474571999755729301)
              ·
                refine ⟨91204053495562488549811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1945686474571999755729301 91204053495562488549811)
                ·
                  rfl

theorem cell22_2397860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 6].length) (baseStart_2397860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397860 prefixEnd_2397860 := by exact prefixLift 2397860
  have htrace : WordTrace (prefixWord ++ tailWord_2397860) baseStart_2397860 baseEnd_2397860 := by
    simpa [prefixWord, tailWord_2397860, baseEnd_2397860] using wordTrace_append hprefix tailTrace_2397860
  have hstable : (prefixWord ++ tailWord_2397860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397860).length < 2 ^ (prefixWord ++ tailWord_2397860).sum := by decide
  have hdescent : baseEnd_2397860 < baseStart_2397860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397877 : List Nat := [1, 3, 3, 3, 3, 1, 8]
def baseStart_2397877 : Nat := 118140960795 + 2397877 * 2 ^ 59
def prefixEnd_2397877 : Nat := 4983230072969 + 3 ^ 40 * 2397877 * 2
def baseEnd_2397877 : Nat := 30401566700277037750861

theorem tailTrace_2397877 : CollatzResearch.WordTrace tailWord_2397877 prefixEnd_2397877 30401566700277037750861 := by
  unfold tailWord_2397877
  simp only [CollatzResearch.WordTrace]
  refine ⟨87457759133908628632775885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58305172755939085755183923 87457759133908628632775885)
  ·
    refine ⟨32796659675215735737290957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87457759133908628632775885 32796659675215735737290957)
    ·
      refine ⟨12298747378205900901484109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32796659675215735737290957 12298747378205900901484109)
      ·
        refine ⟨4612030266827212838056541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12298747378205900901484109 4612030266827212838056541)
        ·
          refine ⟨1729511350060204814271203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4612030266827212838056541 1729511350060204814271203)
          ·
            refine ⟨2594267025090307221406805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729511350060204814271203 2594267025090307221406805)
            ·
              refine ⟨30401566700277037750861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2594267025090307221406805 30401566700277037750861)
              ·
                rfl

theorem cell22_2397877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 8].length) (baseStart_2397877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397877 prefixEnd_2397877 := by exact prefixLift 2397877
  have htrace : WordTrace (prefixWord ++ tailWord_2397877) baseStart_2397877 baseEnd_2397877 := by
    simpa [prefixWord, tailWord_2397877, baseEnd_2397877] using wordTrace_append hprefix tailTrace_2397877
  have hstable : (prefixWord ++ tailWord_2397877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397877).length < 2 ^ (prefixWord ++ tailWord_2397877).sum := by decide
  have hdescent : baseEnd_2397877 < baseStart_2397877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397888 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_2397888 : Nat := 118140960795 + 2397888 * 2 ^ 59
def prefixEnd_2397888 : Nat := 4983230072969 + 3 ^ 40 * 2397888 * 2
def baseEnd_2397888 : Nat := 273615355477426552416071

theorem tailTrace_2397888 : CollatzResearch.WordTrace tailWord_2397888 prefixEnd_2397888 273615355477426552416071 := by
  unfold tailWord_2397888
  simp only [CollatzResearch.WordTrace]
  refine ⟨43729080168434388755713159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58305440224579185007617545 43729080168434388755713159)
  ·
    refine ⟨65593620252651583133569739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43729080168434388755713159 65593620252651583133569739)
    ·
      refine ⟨98390430378977374700354609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65593620252651583133569739 98390430378977374700354609)
      ·
        refine ⟨73792822784233031025265957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98390430378977374700354609 73792822784233031025265957)
        ·
          refine ⟨13836154272043693317237367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73792822784233031025265957 13836154272043693317237367)
          ·
            refine ⟨20754231408065539975856051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13836154272043693317237367 20754231408065539975856051)
            ·
              refine ⟨31131347112098309963784077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20754231408065539975856051 31131347112098309963784077)
              ·
                refine ⟨11674255167036866236419029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31131347112098309963784077 11674255167036866236419029)
                ·
                  refine ⟨273615355477426552416071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11674255167036866236419029 273615355477426552416071)
                  ·
                    rfl

theorem cell22_2397888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_2397888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397888 prefixEnd_2397888 := by exact prefixLift 2397888
  have htrace : WordTrace (prefixWord ++ tailWord_2397888) baseStart_2397888 baseEnd_2397888 := by
    simpa [prefixWord, tailWord_2397888, baseEnd_2397888] using wordTrace_append hprefix tailTrace_2397888
  have hstable : (prefixWord ++ tailWord_2397888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397888).length < 2 ^ (prefixWord ++ tailWord_2397888).sum := by decide
  have hdescent : baseEnd_2397888 < baseStart_2397888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397894 : List Nat := [6, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2397894 : Nat := 118140960795 + 2397894 * 2 ^ 59
def prefixEnd_2397894 : Nat := 4983230072969 + 3 ^ 40 * 2397894 * 2
def baseEnd_2397894 : Nat := 91205346706099737955355

theorem tailTrace_2397894 : CollatzResearch.WordTrace tailWord_2397894 prefixEnd_2397894 91205346706099737955355 := by
  unfold tailWord_2397894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2733074349213970016754523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58305586116564693690763157 2733074349213970016754523)
  ·
    refine ⟨4099611523820955025131785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2733074349213970016754523 4099611523820955025131785)
    ·
      refine ⟨3074708642865716268848839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4099611523820955025131785 3074708642865716268848839)
      ·
        refine ⟨4612062964298574403273259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3074708642865716268848839 4612062964298574403273259)
        ·
          refine ⟨6918094446447861604909889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4612062964298574403273259 6918094446447861604909889)
          ·
            refine ⟨5188570834835896203682417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6918094446447861604909889 5188570834835896203682417)
            ·
              refine ⟨3891428126126922152761813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5188570834835896203682417 3891428126126922152761813)
              ·
                refine ⟨91205346706099737955355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3891428126126922152761813 91205346706099737955355)
                ·
                  rfl

theorem cell22_2397894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2397894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397894 prefixEnd_2397894 := by exact prefixLift 2397894
  have htrace : WordTrace (prefixWord ++ tailWord_2397894) baseStart_2397894 baseEnd_2397894 := by
    simpa [prefixWord, tailWord_2397894, baseEnd_2397894] using wordTrace_append hprefix tailTrace_2397894
  have hstable : (prefixWord ++ tailWord_2397894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397894).length < 2 ^ (prefixWord ++ tailWord_2397894).sum := by decide
  have hdescent : baseEnd_2397894 < baseStart_2397894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397903 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_2397903 : Nat := 118140960795 + 2397903 * 2 ^ 59
def prefixEnd_2397903 : Nat := 4983230072969 + 3 ^ 40 * 2397903 * 2
def baseEnd_2397903 : Nat := 820851201238824618123167

theorem tailTrace_2397903 : CollatzResearch.WordTrace tailWord_2397903 prefixEnd_2397903 820851201238824618123167 := by
  unfold tailWord_2397903
  simp only [CollatzResearch.WordTrace]
  refine ⟨87458707431814435073222363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58305804954542956715481575 87458707431814435073222363)
  ·
    refine ⟨131188061147721652609833545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87458707431814435073222363 131188061147721652609833545)
    ·
      refine ⟨98391045860791239457375159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131188061147721652609833545 98391045860791239457375159)
      ·
        refine ⟨147586568791186859186062739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98391045860791239457375159 147586568791186859186062739)
        ·
          refine ⟨221379853186780288779094109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147586568791186859186062739 221379853186780288779094109)
          ·
            refine ⟨83017444945042608292160291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221379853186780288779094109 83017444945042608292160291)
            ·
              refine ⟨124526167417563912438240437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83017444945042608292160291 124526167417563912438240437)
              ·
                refine ⟨11674328195396616791085041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124526167417563912438240437 11674328195396616791085041)
                ·
                  refine ⟨8755746146547462593313781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11674328195396616791085041 8755746146547462593313781)
                  ·
                    refine ⟨820851201238824618123167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8755746146547462593313781 820851201238824618123167)
                    ·
                      rfl

theorem cell22_2397903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_2397903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397903 prefixEnd_2397903 := by exact prefixLift 2397903
  have htrace : WordTrace (prefixWord ++ tailWord_2397903) baseStart_2397903 baseEnd_2397903 := by
    simpa [prefixWord, tailWord_2397903, baseEnd_2397903] using wordTrace_append hprefix tailTrace_2397903
  have hstable : (prefixWord ++ tailWord_2397903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397903).length < 2 ^ (prefixWord ++ tailWord_2397903).sum := by decide
  have hdescent : baseEnd_2397903 < baseStart_2397903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397905 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 5]
def baseStart_2397905 : Nat := 118140960795 + 2397905 * 2 ^ 59
def prefixEnd_2397905 : Nat := 4983230072969 + 3 ^ 40 * 2397905 * 2
def baseEnd_2397905 : Nat := 273617295293232426524387

theorem tailTrace_2397905 : CollatzResearch.WordTrace tailWord_2397905 prefixEnd_2397905 273617295293232426524387 := by
  unfold tailWord_2397905
  simp only [CollatzResearch.WordTrace]
  refine ⟨87458780377807189414795169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58305853585204792943196779 87458780377807189414795169)
  ·
    refine ⟨65594085283355392061096377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87458780377807189414795169 65594085283355392061096377)
    ·
      refine ⟨49195563962516544045822283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65594085283355392061096377 49195563962516544045822283)
      ·
        refine ⟨73793345943774816068733425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49195563962516544045822283 73793345943774816068733425)
        ·
          refine ⟨55345009457831112051550069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73793345943774816068733425 55345009457831112051550069)
          ·
            refine ⟨5188594636671666754832819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55345009457831112051550069 5188594636671666754832819)
            ·
              refine ⟨7782891955007500132249229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188594636671666754832819 7782891955007500132249229)
              ·
                refine ⟨2918584483127812549593461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7782891955007500132249229 2918584483127812549593461)
                ·
                  refine ⟨273617295293232426524387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918584483127812549593461 273617295293232426524387)
                  ·
                    rfl

theorem cell22_2397905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_2397905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397905 prefixEnd_2397905 := by exact prefixLift 2397905
  have htrace : WordTrace (prefixWord ++ tailWord_2397905) baseStart_2397905 baseEnd_2397905 := by
    simpa [prefixWord, tailWord_2397905, baseEnd_2397905] using wordTrace_append hprefix tailTrace_2397905
  have hstable : (prefixWord ++ tailWord_2397905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397905).length < 2 ^ (prefixWord ++ tailWord_2397905).sum := by decide
  have hdescent : baseEnd_2397905 < baseStart_2397905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397980 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2397980 : Nat := 118140960795 + 2397980 * 2 ^ 59
def prefixEnd_2397980 : Nat := 4983230072969 + 3 ^ 40 * 2397980 * 2
def baseEnd_2397980 : Nat := 820877559912422083947931

theorem tailTrace_2397980 : CollatzResearch.WordTrace tailWord_2397980 prefixEnd_2397980 820877559912422083947931 := by
  unfold tailWord_2397980
  simp only [CollatzResearch.WordTrace]
  refine ⟨43730757926267738611887697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58307677235023651482516929 43730757926267738611887697)
  ·
    refine ⟨32798068444700803958915773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43730757926267738611887697 32798068444700803958915773)
    ·
      refine ⟨12299275666762801484593415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32798068444700803958915773 12299275666762801484593415)
      ·
        refine ⟨18448913500144202226890123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12299275666762801484593415 18448913500144202226890123)
        ·
          refine ⟨27673370250216303340335185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18448913500144202226890123 27673370250216303340335185)
          ·
            refine ⟨20755027687662227505251389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27673370250216303340335185 20755027687662227505251389)
            ·
              refine ⟨7783135382873335314469271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20755027687662227505251389 7783135382873335314469271)
              ·
                refine ⟨11674703074310002971703907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7783135382873335314469271 11674703074310002971703907)
                ·
                  refine ⟨17512054611465004457555861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11674703074310002971703907 17512054611465004457555861)
                  ·
                    refine ⟨820877559912422083947931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17512054611465004457555861 820877559912422083947931)
                    ·
                      rfl

theorem cell22_2397980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2397980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2397980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2397980 prefixEnd_2397980 := by exact prefixLift 2397980
  have htrace : WordTrace (prefixWord ++ tailWord_2397980) baseStart_2397980 baseEnd_2397980 := by
    simpa [prefixWord, tailWord_2397980, baseEnd_2397980] using wordTrace_append hprefix tailTrace_2397980
  have hstable : (prefixWord ++ tailWord_2397980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397980).length < 2 ^ (prefixWord ++ tailWord_2397980).sum := by decide
  have hdescent : baseEnd_2397980 < baseStart_2397980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398029 : List Nat := [1, 6, 1, 2, 1, 1, 4, 6]
def baseStart_2398029 : Nat := 118140960795 + 2398029 * 2 ^ 59
def prefixEnd_2398029 : Nat := 4983230072969 + 3 ^ 40 * 2398029 * 2
def baseEnd_2398029 : Nat := 91210481512644698830309

theorem tailTrace_2398029 : CollatzResearch.WordTrace tailWord_2398029 prefixEnd_2398029 91210481512644698830309 := by
  unfold tailWord_2398029
  simp only [CollatzResearch.WordTrace]
  refine ⟨87463303029357958592309141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58308868686238639061539427 87463303029357958592309141)
  ·
    refine ⟨4099842329501154309014491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87463303029357958592309141 4099842329501154309014491)
    ·
      refine ⟨6149763494251731463521737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4099842329501154309014491 6149763494251731463521737)
      ·
        refine ⟨4612322620688798597641303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6149763494251731463521737 4612322620688798597641303)
        ·
          refine ⟨6918483931033197896461955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4612322620688798597641303 6918483931033197896461955)
          ·
            refine ⟨10377725896549796844692933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6918483931033197896461955 10377725896549796844692933)
            ·
              refine ⟨1945823605603086908379925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10377725896549796844692933 1945823605603086908379925)
              ·
                refine ⟨91210481512644698830309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1945823605603086908379925 91210481512644698830309)
                ·
                  rfl

theorem cell22_2398029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 6].length) (baseStart_2398029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398029 prefixEnd_2398029 := by exact prefixLift 2398029
  have htrace : WordTrace (prefixWord ++ tailWord_2398029) baseStart_2398029 baseEnd_2398029 := by
    simpa [prefixWord, tailWord_2398029, baseEnd_2398029] using wordTrace_append hprefix tailTrace_2398029
  have hstable : (prefixWord ++ tailWord_2398029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398029).length < 2 ^ (prefixWord ++ tailWord_2398029).sum := by decide
  have hdescent : baseEnd_2398029 < baseStart_2398029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398085 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 8]
def baseStart_2398085 : Nat := 118140960795 + 2398085 * 2 ^ 59
def prefixEnd_2398085 : Nat := 4983230072969 + 3 ^ 40 * 2398085 * 2
def baseEnd_2398085 : Nat := 273637834519412270024203

theorem tailTrace_2398085 : CollatzResearch.WordTrace tailWord_2398085 prefixEnd_2398085 273637834519412270024203 := by
  unfold tailWord_2398085
  simp only [CollatzResearch.WordTrace]
  refine ⟨87465345517155080156347709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58310230344770053437565139 87465345517155080156347709)
  ·
    refine ⟨32799504568933155058630391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87465345517155080156347709 32799504568933155058630391)
    ·
      refine ⟨49199256853399732587945587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32799504568933155058630391 49199256853399732587945587)
      ·
        refine ⟨73798885280099598881918381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49199256853399732587945587 73798885280099598881918381)
        ·
          refine ⟨27674581980037349580719393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73798885280099598881918381 27674581980037349580719393)
          ·
            refine ⟨20755936485028012185539545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27674581980037349580719393 20755936485028012185539545)
            ·
              refine ⟨15566952363771009139154659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20755936485028012185539545 15566952363771009139154659)
              ·
                refine ⟨23350428545656513708731989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15566952363771009139154659 23350428545656513708731989)
                ·
                  refine ⟨273637834519412270024203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23350428545656513708731989 273637834519412270024203)
                  ·
                    rfl

theorem cell22_2398085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_2398085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398085 prefixEnd_2398085 := by exact prefixLift 2398085
  have htrace : WordTrace (prefixWord ++ tailWord_2398085) baseStart_2398085 baseEnd_2398085 := by
    simpa [prefixWord, tailWord_2398085, baseEnd_2398085] using wordTrace_append hprefix tailTrace_2398085
  have hstable : (prefixWord ++ tailWord_2398085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398085).length < 2 ^ (prefixWord ++ tailWord_2398085).sum := by decide
  have hdescent : baseEnd_2398085 < baseStart_2398085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398115 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_2398115 : Nat := 118140960795 + 2398115 * 2 ^ 59
def prefixEnd_2398115 : Nat := 4983230072969 + 3 ^ 40 * 2398115 * 2
def baseEnd_2398115 : Nat := 820923773171326731822517

theorem tailTrace_2398115 : CollatzResearch.WordTrace tailWord_2398115 prefixEnd_2398115 820923773171326731822517 := by
  unfold tailWord_2398115
  simp only [CollatzResearch.WordTrace]
  refine ⟨87466439707046395279939799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58310959804697596853293199 87466439707046395279939799)
  ·
    refine ⟨131199659560569592919909699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87466439707046395279939799 131199659560569592919909699)
    ·
      refine ⟨196799489340854389379864549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131199659560569592919909699 196799489340854389379864549)
      ·
        refine ⟨36899904251410198008724603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196799489340854389379864549 36899904251410198008724603)
        ·
          refine ⟨55349856377115297013086905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36899904251410198008724603 55349856377115297013086905)
          ·
            refine ⟨41512392282836472759815179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55349856377115297013086905 41512392282836472759815179)
            ·
              refine ⟨62268588424254709139722769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41512392282836472759815179 62268588424254709139722769)
              ·
                refine ⟨46701441318191031854792077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62268588424254709139722769 46701441318191031854792077)
                ·
                  refine ⟨17513040494321636945547029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46701441318191031854792077 17513040494321636945547029)
                  ·
                    refine ⟨820923773171326731822517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17513040494321636945547029 820923773171326731822517)
                    ·
                      rfl

theorem cell22_2398115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_2398115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398115 prefixEnd_2398115 := by exact prefixLift 2398115
  have htrace : WordTrace (prefixWord ++ tailWord_2398115) baseStart_2398115 baseEnd_2398115 := by
    simpa [prefixWord, tailWord_2398115, baseEnd_2398115] using wordTrace_append hprefix tailTrace_2398115
  have hstable : (prefixWord ++ tailWord_2398115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398115).length < 2 ^ (prefixWord ++ tailWord_2398115).sum := by decide
  have hdescent : baseEnd_2398115 < baseStart_2398115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398117 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_2398117 : Nat := 118140960795 + 2398117 * 2 ^ 59
def prefixEnd_2398117 : Nat := 4983230072969 + 3 ^ 40 * 2398117 * 2
def baseEnd_2398117 : Nat := 820924457812199393272511

theorem tailTrace_2398117 : CollatzResearch.WordTrace tailWord_2398117 prefixEnd_2398117 820924457812199393272511 := by
  unfold tailWord_2398117
  simp only [CollatzResearch.WordTrace]
  refine ⟨87466512653039149621512605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58311008435359433081008403 87466512653039149621512605)
  ·
    refine ⟨32799942244889681108067227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87466512653039149621512605 32799942244889681108067227)
    ·
      refine ⟨49199913367334521662100841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32799942244889681108067227 49199913367334521662100841)
      ·
        refine ⟨36899935025500891246575631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49199913367334521662100841 36899935025500891246575631)
        ·
          refine ⟨55349902538251336869863447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36899935025500891246575631 55349902538251336869863447)
          ·
            refine ⟨83024853807377005304795171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55349902538251336869863447 83024853807377005304795171)
            ·
              refine ⟨124537280711065507957192757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83024853807377005304795171 124537280711065507957192757)
              ·
                refine ⟨11675370066662391370986821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124537280711065507957192757 11675370066662391370986821)
                ·
                  refine ⟨2189131887499198382060029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11675370066662391370986821 2189131887499198382060029)
                  ·
                    refine ⟨820924457812199393272511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189131887499198382060029 820924457812199393272511)
                    ·
                      rfl

theorem cell22_2398117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_2398117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398117 prefixEnd_2398117 := by exact prefixLift 2398117
  have htrace : WordTrace (prefixWord ++ tailWord_2398117) baseStart_2398117 baseEnd_2398117 := by
    simpa [prefixWord, tailWord_2398117, baseEnd_2398117] using wordTrace_append hprefix tailTrace_2398117
  have hstable : (prefixWord ++ tailWord_2398117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398117).length < 2 ^ (prefixWord ++ tailWord_2398117).sum := by decide
  have hdescent : baseEnd_2398117 < baseStart_2398117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398179 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 3, 3]
def baseStart_2398179 : Nat := 118140960795 + 2398179 * 2 ^ 59
def prefixEnd_2398179 : Nat := 4983230072969 + 3 ^ 40 * 2398179 * 2
def baseEnd_2398179 : Nat := 820945681679251898222321

theorem tailTrace_2398179 : CollatzResearch.WordTrace tailWord_2398179 prefixEnd_2398179 820945681679251898222321 := by
  unfold tailWord_2398179
  simp only [CollatzResearch.WordTrace]
  refine ⟨87468773978814534210269591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58312515985876356140179727 87468773978814534210269591)
  ·
    refine ⟨131203160968221801315404387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87468773978814534210269591 131203160968221801315404387)
    ·
      refine ⟨196804741452332701973106581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131203160968221801315404387 196804741452332701973106581)
      ·
        refine ⟨9225222255578095404989371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 196804741452332701973106581 9225222255578095404989371)
        ·
          refine ⟨13837833383367143107484057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225222255578095404989371 13837833383367143107484057)
          ·
            refine ⟨10378375037525357330613043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13837833383367143107484057 10378375037525357330613043)
            ·
              refine ⟨15567562556288035995919565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10378375037525357330613043 15567562556288035995919565)
              ·
                refine ⟨5837835958608013498469837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15567562556288035995919565 5837835958608013498469837)
                ·
                  refine ⟨2189188484478005061926189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5837835958608013498469837 2189188484478005061926189)
                  ·
                    refine ⟨820945681679251898222321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189188484478005061926189 820945681679251898222321)
                    ·
                      rfl

theorem cell22_2398179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 3].length) (baseStart_2398179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398179 prefixEnd_2398179 := by exact prefixLift 2398179
  have htrace : WordTrace (prefixWord ++ tailWord_2398179) baseStart_2398179 baseEnd_2398179 := by
    simpa [prefixWord, tailWord_2398179, baseEnd_2398179] using wordTrace_append hprefix tailTrace_2398179
  have hstable : (prefixWord ++ tailWord_2398179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398179).length < 2 ^ (prefixWord ++ tailWord_2398179).sum := by decide
  have hdescent : baseEnd_2398179 < baseStart_2398179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398192 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_2398192 : Nat := 118140960795 + 2398192 * 2 ^ 59
def prefixEnd_2398192 : Nat := 4983230072969 + 3 ^ 40 * 2398192 * 2
def baseEnd_2398192 : Nat := 273650043948308065882427

theorem tailTrace_2398192 : CollatzResearch.WordTrace tailWord_2398192 prefixEnd_2398192 273650043948308065882427 := by
  unfold tailWord_2398192
  simp only [CollatzResearch.WordTrace]
  refine ⟨43734624063883718715246415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58312832085178291620328553 43734624063883718715246415)
  ·
    refine ⟨65601936095825578072869623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43734624063883718715246415 65601936095825578072869623)
    ·
      refine ⟨98402904143738367109304435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65601936095825578072869623 98402904143738367109304435)
      ·
        refine ⟨147604356215607550663956653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98402904143738367109304435 147604356215607550663956653)
        ·
          refine ⟨55351633580852831498983745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147604356215607550663956653 55351633580852831498983745)
          ·
            refine ⟨41513725185639623624237809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55351633580852831498983745 41513725185639623624237809)
            ·
              refine ⟨31135293889229717718178357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41513725185639623624237809 31135293889229717718178357)
              ·
                refine ⟨2918933802115286036079221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31135293889229717718178357 2918933802115286036079221)
                ·
                  refine ⟨273650043948308065882427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918933802115286036079221 273650043948308065882427)
                  ·
                    rfl

theorem cell22_2398192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_2398192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398192 prefixEnd_2398192 := by exact prefixLift 2398192
  have htrace : WordTrace (prefixWord ++ tailWord_2398192) baseStart_2398192 baseEnd_2398192 := by
    simpa [prefixWord, tailWord_2398192, baseEnd_2398192] using wordTrace_append hprefix tailTrace_2398192
  have hstable : (prefixWord ++ tailWord_2398192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398192).length < 2 ^ (prefixWord ++ tailWord_2398192).sum := by decide
  have hdescent : baseEnd_2398192 < baseStart_2398192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398198 : List Nat := [5, 1, 1, 1, 5, 1, 2, 6]
def baseStart_2398198 : Nat := 118140960795 + 2398198 * 2 ^ 59
def prefixEnd_2398198 : Nat := 4983230072969 + 3 ^ 40 * 2398198 * 2
def baseEnd_2398198 : Nat := 91216909529726909110807

theorem tailTrace_2398198 : CollatzResearch.WordTrace tailWord_2398198 prefixEnd_2398198 91216909529726909110807 := by
  unfold tailWord_2398198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466841685359106278450703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58312977977163800303474165 5466841685359106278450703)
  ·
    refine ⟨8200262528038659417676055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5466841685359106278450703 8200262528038659417676055)
    ·
      refine ⟨12300393792057989126514083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8200262528038659417676055 12300393792057989126514083)
      ·
        refine ⟨18450590688086983689771125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12300393792057989126514083 18450590688086983689771125)
        ·
          refine ⟨1729742877008154720916043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18450590688086983689771125 1729742877008154720916043)
          ·
            refine ⟨2594614315512232081374065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729742877008154720916043 2594614315512232081374065)
            ·
              refine ⟨1945960736634174061030549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594614315512232081374065 1945960736634174061030549)
              ·
                refine ⟨91216909529726909110807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1945960736634174061030549 91216909529726909110807)
                ·
                  rfl

theorem cell22_2398198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_2398198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398198 prefixEnd_2398198 := by exact prefixLift 2398198
  have htrace : WordTrace (prefixWord ++ tailWord_2398198) baseStart_2398198 baseEnd_2398198 := by
    simpa [prefixWord, tailWord_2398198, baseEnd_2398198] using wordTrace_append hprefix tailTrace_2398198
  have hstable : (prefixWord ++ tailWord_2398198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398198).length < 2 ^ (prefixWord ++ tailWord_2398198).sum := by decide
  have hdescent : baseEnd_2398198 < baseStart_2398198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398213 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_2398213 : Nat := 118140960795 + 2398213 * 2 ^ 59
def prefixEnd_2398213 : Nat := 4983230072969 + 3 ^ 40 * 2398213 * 2
def baseEnd_2398213 : Nat := 820957320574087142872217

theorem tailTrace_2398213 : CollatzResearch.WordTrace tailWord_2398213 prefixEnd_2398213 820957320574087142872217 := by
  unfold tailWord_2398213
  simp only [CollatzResearch.WordTrace]
  refine ⟨87470014060691358017007293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58313342707127572011338195 87470014060691358017007293)
  ·
    refine ⟨32801255272759259256377735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87470014060691358017007293 32801255272759259256377735)
    ·
      refine ⟨49201882909138888884566603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32801255272759259256377735 49201882909138888884566603)
      ·
        refine ⟨73802824363708333326849905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49201882909138888884566603 73802824363708333326849905)
        ·
          refine ⟨55352118272781249995137429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73802824363708333326849905 55352118272781249995137429)
          ·
            refine ⟨2594630544036621093522067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55352118272781249995137429 2594630544036621093522067)
            ·
              refine ⟨3891945816054931640283101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594630544036621093522067 3891945816054931640283101)
              ·
                refine ⟨1459479681020599365106163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3891945816054931640283101 1459479681020599365106163)
                ·
                  refine ⟨2189219521530899047659245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459479681020599365106163 2189219521530899047659245)
                  ·
                    refine ⟨820957320574087142872217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189219521530899047659245 820957320574087142872217)
                    ·
                      rfl

theorem cell22_2398213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_2398213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398213 prefixEnd_2398213 := by exact prefixLift 2398213
  have htrace : WordTrace (prefixWord ++ tailWord_2398213) baseStart_2398213 baseEnd_2398213 := by
    simpa [prefixWord, tailWord_2398213, baseEnd_2398213] using wordTrace_append hprefix tailTrace_2398213
  have hstable : (prefixWord ++ tailWord_2398213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398213).length < 2 ^ (prefixWord ++ tailWord_2398213).sum := by decide
  have hdescent : baseEnd_2398213 < baseStart_2398213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398256 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_2398256 : Nat := 118140960795 + 2398256 * 2 ^ 59
def prefixEnd_2398256 : Nat := 4983230072969 + 3 ^ 40 * 2398256 * 2
def baseEnd_2398256 : Nat := 820972040352849364047085

theorem tailTrace_2398256 : CollatzResearch.WordTrace tailWord_2398256 prefixEnd_2398256 820972040352849364047085 := by
  unfold tailWord_2398256
  simp only [CollatzResearch.WordTrace]
  refine ⟨43735791199767788180411311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58314388266357050907215081 43735791199767788180411311)
  ·
    refine ⟨65603686799651682270616967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43735791199767788180411311 65603686799651682270616967)
    ·
      refine ⟨98405530199477523405925451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65603686799651682270616967 98405530199477523405925451)
      ·
        refine ⟨147608295299216285108888177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98405530199477523405925451 147608295299216285108888177)
        ·
          refine ⟨110706221474412213831666133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147608295299216285108888177 110706221474412213831666133)
          ·
            refine ⟨2594677065806536261679675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110706221474412213831666133 2594677065806536261679675)
            ·
              refine ⟨3892015598709804392519513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594677065806536261679675 3892015598709804392519513)
              ·
                refine ⟨2919011699032353294389635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892015598709804392519513 2919011699032353294389635)
                ·
                  refine ⟨4378517548548529941584453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919011699032353294389635 4378517548548529941584453)
                  ·
                    refine ⟨820972040352849364047085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378517548548529941584453 820972040352849364047085)
                    ·
                      rfl

theorem cell22_2398256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_2398256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398256 prefixEnd_2398256 := by exact prefixLift 2398256
  have htrace : WordTrace (prefixWord ++ tailWord_2398256) baseStart_2398256 baseEnd_2398256 := by
    simpa [prefixWord, tailWord_2398256, baseEnd_2398256] using wordTrace_append hprefix tailTrace_2398256
  have hstable : (prefixWord ++ tailWord_2398256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398256).length < 2 ^ (prefixWord ++ tailWord_2398256).sum := by decide
  have hdescent : baseEnd_2398256 < baseStart_2398256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 6, 4]
def baseStart_2398267 : Nat := 118140960795 + 2398267 * 2 ^ 59
def prefixEnd_2398267 : Nat := 4983230072969 + 3 ^ 40 * 2398267 * 2
def baseEnd_2398267 : Nat := 820975805877649002022051

theorem tailTrace_2398267 : CollatzResearch.WordTrace tailWord_2398267 prefixEnd_2398267 820975805877649002022051 := by
  unfold tailWord_2398267
  simp only [CollatzResearch.WordTrace]
  refine ⟨87471983602495725239473055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58314655734997150159648703 87471983602495725239473055)
  ·
    refine ⟨131207975403743587859209583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87471983602495725239473055 131207975403743587859209583)
    ·
      refine ⟨196811963105615381788814375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131207975403743587859209583 196811963105615381788814375)
      ·
        refine ⟨295217944658423072683221563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196811963105615381788814375 295217944658423072683221563)
        ·
          refine ⟨442826916987634609024832345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295217944658423072683221563 442826916987634609024832345)
          ·
            refine ⟨332120187740725956768624259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442826916987634609024832345 332120187740725956768624259)
            ·
              refine ⟨498180281611088935152936389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332120187740725956768624259 498180281611088935152936389)
              ·
                refine ⟨93408802802079175341175573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498180281611088935152936389 93408802802079175341175573)
                ·
                  refine ⟨4378537631347461344117605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93408802802079175341175573 4378537631347461344117605)
                  ·
                    refine ⟨820975805877649002022051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378537631347461344117605 820975805877649002022051)
                    ·
                      rfl

theorem cell22_2398267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_2398267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398267 prefixEnd_2398267 := by exact prefixLift 2398267
  have htrace : WordTrace (prefixWord ++ tailWord_2398267) baseStart_2398267 baseEnd_2398267 := by
    simpa [prefixWord, tailWord_2398267, baseEnd_2398267] using wordTrace_append hprefix tailTrace_2398267
  have hstable : (prefixWord ++ tailWord_2398267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398267).length < 2 ^ (prefixWord ++ tailWord_2398267).sum := by decide
  have hdescent : baseEnd_2398267 < baseStart_2398267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398269 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2398269 : Nat := 118140960795 + 2398269 * 2 ^ 59
def prefixEnd_2398269 : Nat := 4983230072969 + 3 ^ 40 * 2398269 * 2
def baseEnd_2398269 : Nat := 820976490518521663472045

theorem tailTrace_2398269 : CollatzResearch.WordTrace tailWord_2398269 prefixEnd_2398269 820976490518521663472045 := by
  unfold tailWord_2398269
  simp only [CollatzResearch.WordTrace]
  refine ⟨87472056548488479581045861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58314704365658986387363907 87472056548488479581045861)
  ·
    refine ⟨16401010602841589921446099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87472056548488479581045861 16401010602841589921446099)
    ·
      refine ⟨24601515904262384882169149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16401010602841589921446099 24601515904262384882169149)
      ·
        refine ⟨9225568464098394330813431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24601515904262384882169149 9225568464098394330813431)
        ·
          refine ⟨13838352696147591496220147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225568464098394330813431 13838352696147591496220147)
          ·
            refine ⟨20757529044221387244330221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838352696147591496220147 20757529044221387244330221)
            ·
              refine ⟨7784073391583020216623833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20757529044221387244330221 7784073391583020216623833)
              ·
                refine ⟨5838055043687265162467875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7784073391583020216623833 5838055043687265162467875)
                ·
                  refine ⟨8757082565530897743701813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838055043687265162467875 8757082565530897743701813)
                  ·
                    refine ⟨820976490518521663472045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8757082565530897743701813 820976490518521663472045)
                    ·
                      rfl

theorem cell22_2398269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2398269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398269 prefixEnd_2398269 := by exact prefixLift 2398269
  have htrace : WordTrace (prefixWord ++ tailWord_2398269) baseStart_2398269 baseEnd_2398269 := by
    simpa [prefixWord, tailWord_2398269, baseEnd_2398269] using wordTrace_append hprefix tailTrace_2398269
  have hstable : (prefixWord ++ tailWord_2398269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398269).length < 2 ^ (prefixWord ++ tailWord_2398269).sum := by decide
  have hdescent : baseEnd_2398269 < baseStart_2398269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398273 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2398273 : Nat := 118140960795 + 2398273 * 2 ^ 59
def prefixEnd_2398273 : Nat := 4983230072969 + 3 ^ 40 * 2398273 * 2
def baseEnd_2398273 : Nat := 820977859800266986372033

theorem tailTrace_2398273 : CollatzResearch.WordTrace tailWord_2398273 prefixEnd_2398273 820977859800266986372033 := by
  unfold tailWord_2398273
  simp only [CollatzResearch.WordTrace]
  refine ⟨87472202440473988264191473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58314801626982658842794315 87472202440473988264191473)
  ·
    refine ⟨65604151830355491198143605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87472202440473988264191473 65604151830355491198143605)
    ·
      refine ⟨6150389234095827299825963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65604151830355491198143605 6150389234095827299825963)
      ·
        refine ⟨9225583851143740949738945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150389234095827299825963 9225583851143740949738945)
        ·
          refine ⟨6919187888357805712304209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9225583851143740949738945 6919187888357805712304209)
          ·
            refine ⟨5189390916268354284228157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6919187888357805712304209 5189390916268354284228157)
            ·
              refine ⟨1946021593600632856585559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5189390916268354284228157 1946021593600632856585559)
              ·
                refine ⟨2919032390400949284878339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946021593600632856585559 2919032390400949284878339)
                ·
                  refine ⟨4378548585601423927317509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919032390400949284878339 4378548585601423927317509)
                  ·
                    refine ⟨820977859800266986372033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378548585601423927317509 820977859800266986372033)
                    ·
                      rfl

theorem cell22_2398273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2398273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398273 prefixEnd_2398273 := by exact prefixLift 2398273
  have htrace : WordTrace (prefixWord ++ tailWord_2398273) baseStart_2398273 baseEnd_2398273 := by
    simpa [prefixWord, tailWord_2398273, baseEnd_2398273] using wordTrace_append hprefix tailTrace_2398273
  have hstable : (prefixWord ++ tailWord_2398273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398273).length < 2 ^ (prefixWord ++ tailWord_2398273).sum := by decide
  have hdescent : baseEnd_2398273 < baseStart_2398273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398284 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_2398284 : Nat := 118140960795 + 2398284 * 2 ^ 59
def prefixEnd_2398284 : Nat := 4983230072969 + 3 ^ 40 * 2398284 * 2
def baseEnd_2398284 : Nat := 820981625325066624346999

theorem tailTrace_2398284 : CollatzResearch.WordTrace tailWord_2398284 prefixEnd_2398284 820981625325066624346999 := by
  unfold tailWord_2398284
  simp only [CollatzResearch.WordTrace]
  refine ⟨43736301821717068571420953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58315069095622758095227937 43736301821717068571420953)
  ·
    refine ⟨32802226366287801428565715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43736301821717068571420953 32802226366287801428565715)
    ·
      refine ⟨49203339549431702142848573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32802226366287801428565715 49203339549431702142848573)
      ·
        refine ⟨18451252331036888303568215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49203339549431702142848573 18451252331036888303568215)
        ·
          refine ⟨27676878496555332455352323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18451252331036888303568215 27676878496555332455352323)
          ·
            refine ⟨41515317744832998683028485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27676878496555332455352323 41515317744832998683028485)
            ·
              refine ⟨7784122077156187253067841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41515317744832998683028485 7784122077156187253067841)
              ·
                refine ⟨5838091557867140439800881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7784122077156187253067841 5838091557867140439800881)
                ·
                  refine ⟨4378568668400355329850661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5838091557867140439800881 4378568668400355329850661)
                  ·
                    refine ⟨820981625325066624346999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378568668400355329850661 820981625325066624346999)
                    ·
                      rfl

theorem cell22_2398284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_2398284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398284 prefixEnd_2398284 := by exact prefixLift 2398284
  have htrace : WordTrace (prefixWord ++ tailWord_2398284) baseStart_2398284 baseEnd_2398284 := by
    simpa [prefixWord, tailWord_2398284, baseEnd_2398284] using wordTrace_append hprefix tailTrace_2398284
  have hstable : (prefixWord ++ tailWord_2398284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398284).length < 2 ^ (prefixWord ++ tailWord_2398284).sum := by decide
  have hdescent : baseEnd_2398284 < baseStart_2398284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398286 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_2398286 : Nat := 118140960795 + 2398286 * 2 ^ 59
def prefixEnd_2398286 : Nat := 4983230072969 + 3 ^ 40 * 2398286 * 2
def baseEnd_2398286 : Nat := 820982309965939285796993

theorem tailTrace_2398286 : CollatzResearch.WordTrace tailWord_2398286 prefixEnd_2398286 820982309965939285796993 := by
  unfold tailWord_2398286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934084573678361435551839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58315117726284594322943141 10934084573678361435551839)
  ·
    refine ⟨16401126860517542153327759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934084573678361435551839 16401126860517542153327759)
    ·
      refine ⟨24601690290776313229991639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16401126860517542153327759 24601690290776313229991639)
      ·
        refine ⟨36902535436164469844987459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24601690290776313229991639 36902535436164469844987459)
        ·
          refine ⟨55353803154246704767481189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36902535436164469844987459 55353803154246704767481189)
          ·
            refine ⟨10378838091421257143902723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55353803154246704767481189 10378838091421257143902723)
            ·
              refine ⟨15568257137131885715854085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10378838091421257143902723 15568257137131885715854085)
              ·
                refine ⟨2919048213212228571722641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15568257137131885715854085 2919048213212228571722641)
                ·
                  refine ⟨2189286159909171428791981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2919048213212228571722641 2189286159909171428791981)
                  ·
                    refine ⟨820982309965939285796993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189286159909171428791981 820982309965939285796993)
                    ·
                      rfl

theorem cell22_2398286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_2398286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398286 prefixEnd_2398286 := by exact prefixLift 2398286
  have htrace : WordTrace (prefixWord ++ tailWord_2398286) baseStart_2398286 baseEnd_2398286 := by
    simpa [prefixWord, tailWord_2398286, baseEnd_2398286] using wordTrace_append hprefix tailTrace_2398286
  have hstable : (prefixWord ++ tailWord_2398286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398286).length < 2 ^ (prefixWord ++ tailWord_2398286).sum := by decide
  have hdescent : baseEnd_2398286 < baseStart_2398286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398391 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 1, 4]
def baseStart_2398391 : Nat := 118140960795 + 2398391 * 2 ^ 59
def prefixEnd_2398391 : Nat := 4983230072969 + 3 ^ 40 * 2398391 * 2
def baseEnd_2398391 : Nat := 821018253611754011921671

theorem tailTrace_2398391 : CollatzResearch.WordTrace tailWord_2398391 prefixEnd_2398391 821018253611754011921671 := by
  unfold tailWord_2398391
  simp only [CollatzResearch.WordTrace]
  refine ⟨87476506254046494416987027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58317670836030996277991351 87476506254046494416987027)
  ·
    refine ⟨131214759381069741625480541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87476506254046494416987027 131214759381069741625480541)
    ·
      refine ⟨49205534767901153109555203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131214759381069741625480541 49205534767901153109555203)
      ·
        refine ⟨73808302151851729664332805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49205534767901153109555203 73808302151851729664332805)
        ·
          refine ⟨13839056653472199312062401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73808302151851729664332805 13839056653472199312062401)
          ·
            refine ⟨10379292490104149484046801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13839056653472199312062401 10379292490104149484046801)
            ·
              refine ⟨7784469367578112113035101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10379292490104149484046801 7784469367578112113035101)
              ·
                refine ⟨2919176012841792042388163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7784469367578112113035101 2919176012841792042388163)
                ·
                  refine ⟨4378764019262688063582245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919176012841792042388163 4378764019262688063582245)
                  ·
                    refine ⟨821018253611754011921671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378764019262688063582245 821018253611754011921671)
                    ·
                      rfl

theorem cell22_2398391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_2398391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398391 prefixEnd_2398391 := by exact prefixLift 2398391
  have htrace : WordTrace (prefixWord ++ tailWord_2398391) baseStart_2398391 baseEnd_2398391 := by
    simpa [prefixWord, tailWord_2398391, baseEnd_2398391] using wordTrace_append hprefix tailTrace_2398391
  have hstable : (prefixWord ++ tailWord_2398391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398391).length < 2 ^ (prefixWord ++ tailWord_2398391).sum := by decide
  have hdescent : baseEnd_2398391 < baseStart_2398391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398412 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 5]
def baseStart_2398412 : Nat := 118140960795 + 2398412 * 2 ^ 59
def prefixEnd_2398412 : Nat := 4983230072969 + 3 ^ 40 * 2398412 * 2
def baseEnd_2398412 : Nat := 273675147446972319048869

theorem tailTrace_2398412 : CollatzResearch.WordTrace tailWord_2398412 prefixEnd_2398412 273675147446972319048869 := by
  unfold tailWord_2398412
  simp only [CollatzResearch.WordTrace]
  refine ⟨43738636093485207501750745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58318181457980276669000993 43738636093485207501750745)
  ·
    refine ⟨32803977070113905626313059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43738636093485207501750745 32803977070113905626313059)
    ·
      refine ⟨49205965605170858439469589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32803977070113905626313059 49205965605170858439469589)
      ·
        refine ⟨2306529637742383989350137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49205965605170858439469589 2306529637742383989350137)
        ·
          refine ⟨1729897228306787992012603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306529637742383989350137 1729897228306787992012603)
          ·
            refine ⟨2594845842460181988018905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729897228306787992012603 2594845842460181988018905)
            ·
              refine ⟨1946134381845136491014179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594845842460181988018905 1946134381845136491014179)
              ·
                refine ⟨2919201572767704736521269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946134381845136491014179 2919201572767704736521269)
                ·
                  refine ⟨273675147446972319048869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2919201572767704736521269 273675147446972319048869)
                  ·
                    rfl

theorem cell22_2398412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_2398412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398412 prefixEnd_2398412 := by exact prefixLift 2398412
  have htrace : WordTrace (prefixWord ++ tailWord_2398412) baseStart_2398412 baseEnd_2398412 := by
    simpa [prefixWord, tailWord_2398412, baseEnd_2398412] using wordTrace_append hprefix tailTrace_2398412
  have hstable : (prefixWord ++ tailWord_2398412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398412).length < 2 ^ (prefixWord ++ tailWord_2398412).sum := by decide
  have hdescent : baseEnd_2398412 < baseStart_2398412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398464 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_2398464 : Nat := 118140960795 + 2398464 * 2 ^ 59
def prefixEnd_2398464 : Nat := 4983230072969 + 3 ^ 40 * 2398464 * 2
def baseEnd_2398464 : Nat := 821043243003606154846447

theorem tailTrace_2398464 : CollatzResearch.WordTrace tailWord_2398464 prefixEnd_2398464 821043243003606154846447 := by
  unfold tailWord_2398464
  simp only [CollatzResearch.WordTrace]
  refine ⟨43739584391391013942197223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58319445855188018589596297 43739584391391013942197223)
  ·
    refine ⟨65609376587086520913295835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43739584391391013942197223 65609376587086520913295835)
    ·
      refine ⟨98414064880629781369943753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65609376587086520913295835 98414064880629781369943753)
      ·
        refine ⟨73810548660472336027457815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98414064880629781369943753 73810548660472336027457815)
        ·
          refine ⟨110715822990708504041186723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73810548660472336027457815 110715822990708504041186723)
          ·
            refine ⟨166073734486062756061780085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110715822990708504041186723 166073734486062756061780085)
            ·
              refine ⟨15569412608068383380791883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166073734486062756061780085 15569412608068383380791883)
              ·
                refine ⟨23354118912102575071187825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15569412608068383380791883 23354118912102575071187825)
                ·
                  refine ⟨17515589184076931303390869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23354118912102575071187825 17515589184076931303390869)
                  ·
                    refine ⟨821043243003606154846447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17515589184076931303390869 821043243003606154846447)
                    ·
                      rfl

theorem cell22_2398464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_2398464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398464 prefixEnd_2398464 := by exact prefixLift 2398464
  have htrace : WordTrace (prefixWord ++ tailWord_2398464) baseStart_2398464 baseEnd_2398464 := by
    simpa [prefixWord, tailWord_2398464, baseEnd_2398464] using wordTrace_append hprefix tailTrace_2398464
  have hstable : (prefixWord ++ tailWord_2398464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398464).length < 2 ^ (prefixWord ++ tailWord_2398464).sum := by decide
  have hdescent : baseEnd_2398464 < baseStart_2398464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398468 : List Nat := [2, 3, 2, 2, 3, 2, 1, 7]
def baseStart_2398468 : Nat := 118140960795 + 2398468 * 2 ^ 59
def prefixEnd_2398468 : Nat := 4983230072969 + 3 ^ 40 * 2398468 * 2
def baseEnd_2398468 : Nat := 91227179142816830860715

theorem tailTrace_2398468 : CollatzResearch.WordTrace tailWord_2398468 prefixEnd_2398468 91227179142816830860715 := by
  unfold tailWord_2398468
  simp only [CollatzResearch.WordTrace]
  refine ⟨43739657337383768283770029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58319543116511691045026705 43739657337383768283770029)
  ·
    refine ⟨16402371501518913106413761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43739657337383768283770029 16402371501518913106413761)
    ·
      refine ⟨12301778626139184829810321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16402371501518913106413761 12301778626139184829810321)
      ·
        refine ⟨9226333969604388622357741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12301778626139184829810321 9226333969604388622357741)
        ·
          refine ⟨3459875238601645733384153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9226333969604388622357741 3459875238601645733384153)
          ·
            refine ⟨2594906428951234300038115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459875238601645733384153 2594906428951234300038115)
            ·
              refine ⟨3892359643426851450057173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594906428951234300038115 3892359643426851450057173)
              ·
                refine ⟨91227179142816830860715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3892359643426851450057173 91227179142816830860715)
                ·
                  rfl

theorem cell22_2398468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 7].length) (baseStart_2398468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398468 prefixEnd_2398468 := by exact prefixLift 2398468
  have htrace : WordTrace (prefixWord ++ tailWord_2398468) baseStart_2398468 baseEnd_2398468 := by
    simpa [prefixWord, tailWord_2398468, baseEnd_2398468] using wordTrace_append hprefix tailTrace_2398468
  have hstable : (prefixWord ++ tailWord_2398468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398468).length < 2 ^ (prefixWord ++ tailWord_2398468).sum := by decide
  have hdescent : baseEnd_2398468 < baseStart_2398468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398500 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_2398500 : Nat := 118140960795 + 2398500 * 2 ^ 59
def prefixEnd_2398500 : Nat := 4983230072969 + 3 ^ 40 * 2398500 * 2
def baseEnd_2398500 : Nat := 821055566539314060946337

theorem tailTrace_2398500 : CollatzResearch.WordTrace tailWord_2398500 prefixEnd_2398500 821055566539314060946337 := by
  unfold tailWord_2398500
  simp only [CollatzResearch.WordTrace]
  refine ⟨43740240905325803016352477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58320321207101070688469969 43740240905325803016352477)
  ·
    refine ⟨16402590339497176131132179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43740240905325803016352477 16402590339497176131132179)
    ·
      refine ⟨24603885509245764196698269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16402590339497176131132179 24603885509245764196698269)
      ·
        refine ⟨9226457065967161573761851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24603885509245764196698269 9226457065967161573761851)
        ·
          refine ⟨13839685598950742360642777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9226457065967161573761851 13839685598950742360642777)
          ·
            refine ⟨10379764199213056770482083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13839685598950742360642777 10379764199213056770482083)
            ·
              refine ⟨15569646298819585155723125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10379764199213056770482083 15569646298819585155723125)
              ·
                refine ⟨1459654340514336108349043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15569646298819585155723125 1459654340514336108349043)
                ·
                  refine ⟨2189481510771504162523565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459654340514336108349043 2189481510771504162523565)
                  ·
                    refine ⟨821055566539314060946337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189481510771504162523565 821055566539314060946337)
                    ·
                      rfl

theorem cell22_2398500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_2398500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398500 prefixEnd_2398500 := by exact prefixLift 2398500
  have htrace : WordTrace (prefixWord ++ tailWord_2398500) baseStart_2398500 baseEnd_2398500 := by
    simpa [prefixWord, tailWord_2398500, baseEnd_2398500] using wordTrace_append hprefix tailTrace_2398500
  have hstable : (prefixWord ++ tailWord_2398500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398500).length < 2 ^ (prefixWord ++ tailWord_2398500).sum := by decide
  have hdescent : baseEnd_2398500 < baseStart_2398500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398571 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 2, 4]
def baseStart_2398571 : Nat := 118140960795 + 2398571 * 2 ^ 59
def prefixEnd_2398571 : Nat := 4983230072969 + 3 ^ 40 * 2398571 * 2
def baseEnd_2398571 : Nat := 821079871290293542421119

theorem tailTrace_2398571 : CollatzResearch.WordTrace tailWord_2398571 prefixEnd_2398571 821079871290293542421119 := by
  unfold tailWord_2398571
  simp only [CollatzResearch.WordTrace]
  refine ⟨87483071393394385158539567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58322047595596256772359711 87483071393394385158539567)
  ·
    refine ⟨131224607090091577737809351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87483071393394385158539567 131224607090091577737809351)
    ·
      refine ⟨196836910635137366606714027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131224607090091577737809351 196836910635137366606714027)
      ·
        refine ⟨295255365952706049910071041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196836910635137366606714027 295255365952706049910071041)
        ·
          refine ⟨221441524464529537432553281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295255365952706049910071041 221441524464529537432553281)
          ·
            refine ⟨166081143348397153074414961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221441524464529537432553281 166081143348397153074414961)
            ·
              refine ⟨124560857511297864805811221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166081143348397153074414961 124560857511297864805811221)
              ·
                refine ⟨5838790195842087412772401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124560857511297864805811221 5838790195842087412772401)
                ·
                  refine ⟨4379092646881565559579301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5838790195842087412772401 4379092646881565559579301)
                  ·
                    refine ⟨821079871290293542421119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379092646881565559579301 821079871290293542421119)
                    ·
                      rfl

theorem cell22_2398571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_2398571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398571 prefixEnd_2398571 := by exact prefixLift 2398571
  have htrace : WordTrace (prefixWord ++ tailWord_2398571) baseStart_2398571 baseEnd_2398571 := by
    simpa [prefixWord, tailWord_2398571, baseEnd_2398571] using wordTrace_append hprefix tailTrace_2398571
  have hstable : (prefixWord ++ tailWord_2398571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398571).length < 2 ^ (prefixWord ++ tailWord_2398571).sum := by decide
  have hdescent : baseEnd_2398571 < baseStart_2398571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398573 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2398573 : Nat := 118140960795 + 2398573 * 2 ^ 59
def prefixEnd_2398573 : Nat := 4983230072969 + 3 ^ 40 * 2398573 * 2
def baseEnd_2398573 : Nat := 821080555931166203871113

theorem tailTrace_2398573 : CollatzResearch.WordTrace tailWord_2398573 prefixEnd_2398573 821080555931166203871113 := by
  unfold tailWord_2398573
  simp only [CollatzResearch.WordTrace]
  refine ⟨87483144339387139500112373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58322096226258093000074915 87483144339387139500112373)
  ·
    refine ⟨8201544781817544328135535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87483144339387139500112373 8201544781817544328135535)
    ·
      refine ⟨12302317172726316492203303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8201544781817544328135535 12302317172726316492203303)
      ·
        refine ⟨18453475759089474738304955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12302317172726316492203303 18453475759089474738304955)
        ·
          refine ⟨27680213638634212107457433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18453475759089474738304955 27680213638634212107457433)
          ·
            refine ⟨20760160228975659080593075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27680213638634212107457433 20760160228975659080593075)
            ·
              refine ⟨31140240343463488620889613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20760160228975659080593075 31140240343463488620889613)
              ·
                refine ⟨11677590128798808232833605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31140240343463488620889613 11677590128798808232833605)
                ·
                  refine ⟨2189548149149776543656301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11677590128798808232833605 2189548149149776543656301)
                  ·
                    refine ⟨821080555931166203871113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189548149149776543656301 821080555931166203871113)
                    ·
                      rfl

theorem cell22_2398573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2398573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398573 prefixEnd_2398573 := by exact prefixLift 2398573
  have htrace : WordTrace (prefixWord ++ tailWord_2398573) baseStart_2398573 baseEnd_2398573 := by
    simpa [prefixWord, tailWord_2398573, baseEnd_2398573] using wordTrace_append hprefix tailTrace_2398573
  have hstable : (prefixWord ++ tailWord_2398573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398573).length < 2 ^ (prefixWord ++ tailWord_2398573).sum := by decide
  have hdescent : baseEnd_2398573 < baseStart_2398573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398594 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2398594 : Nat := 118140960795 + 2398594 * 2 ^ 59
def prefixEnd_2398594 : Nat := 4983230072969 + 3 ^ 40 * 2398594 * 2
def baseEnd_2398594 : Nat := 821087744660329149096049

theorem tailTrace_2398594 : CollatzResearch.WordTrace tailWord_2398594 prefixEnd_2398594 821087744660329149096049 := by
  unfold tailWord_2398594
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870977568077765021656709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58322606848207373391084557 21870977568077765021656709)
  ·
    refine ⟨4100808294014580941560633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21870977568077765021656709 4100808294014580941560633)
    ·
      refine ⟨3075606220510935706170475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4100808294014580941560633 3075606220510935706170475)
      ·
        refine ⟨4613409330766403559255713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3075606220510935706170475 4613409330766403559255713)
        ·
          refine ⟨3460056998074802669441785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4613409330766403559255713 3460056998074802669441785)
          ·
            refine ⟨2595042748556102002081339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3460056998074802669441785 2595042748556102002081339)
            ·
              refine ⟨3892564122834153003122009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595042748556102002081339 3892564122834153003122009)
              ·
                refine ⟨2919423092125614752341507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892564122834153003122009 2919423092125614752341507)
                ·
                  refine ⟨4379134638188422128512261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919423092125614752341507 4379134638188422128512261)
                  ·
                    refine ⟨821087744660329149096049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379134638188422128512261 821087744660329149096049)
                    ·
                      rfl

theorem cell22_2398594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2398594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2398594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2398594 prefixEnd_2398594 := by exact prefixLift 2398594
  have htrace : WordTrace (prefixWord ++ tailWord_2398594) baseStart_2398594 baseEnd_2398594 := by
    simpa [prefixWord, tailWord_2398594, baseEnd_2398594] using wordTrace_append hprefix tailTrace_2398594
  have hstable : (prefixWord ++ tailWord_2398594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398594).length < 2 ^ (prefixWord ++ tailWord_2398594).sum := by decide
  have hdescent : baseEnd_2398594 < baseStart_2398594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
