import V185TrunkScan20Chunk136

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_832284 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 2]
def baseStart_832284 : Nat := 118140960795 + 832284 * 2 ^ 59
def prefixEnd_832284 : Nat := 4983230072969 + 3 ^ 40 * 832284 * 2
def baseEnd_832284 : Nat := 379877096041535038864357

theorem tailTrace_832284 : CollatzResearch.WordTrace tailWord_832284 prefixEnd_832284 379877096041535038864357 := by
  unfold tailWord_832284
  simp only [CollatzResearch.WordTrace]
  refine ⟨15177945658392342817871953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20237260877856457090495937 15177945658392342817871953)
  ·
    refine ⟨11383459243794257113403965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15177945658392342817871953 11383459243794257113403965)
    ·
      refine ⟨4268797216422846417526487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11383459243794257113403965 4268797216422846417526487)
      ·
        refine ⟨6403195824634269626289731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4268797216422846417526487 6403195824634269626289731)
        ·
          refine ⟨9604793736951404439434597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403195824634269626289731 9604793736951404439434597)
          ·
            refine ⟨1800898825678388332393987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9604793736951404439434597 1800898825678388332393987)
            ·
              refine ⟨2701348238517582498590981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800898825678388332393987 2701348238517582498590981)
              ·
                refine ⟨506502794722046718485809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2701348238517582498590981 506502794722046718485809)
                ·
                  refine ⟨379877096041535038864357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506502794722046718485809 379877096041535038864357)
                  ·
                    rfl

theorem cell20_832284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_832284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832284 prefixEnd_832284 := by exact prefixLift 832284
  have htrace : WordTrace (prefixWord ++ tailWord_832284) baseStart_832284 baseEnd_832284 := by
    simpa [prefixWord, tailWord_832284, baseEnd_832284] using wordTrace_append hprefix tailTrace_832284
  have hstable : (prefixWord ++ tailWord_832284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832284).length < 2 ^ (prefixWord ++ tailWord_832284).sum := by decide
  have hdescent : baseEnd_832284 < baseStart_832284 := by decide
  rcases family_descends (prefixWord ++ tailWord_832284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832301 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 4]
def baseStart_832301 : Nat := 118140960795 + 832301 * 2 ^ 59
def prefixEnd_832301 : Nat := 4983230072969 + 3 ^ 40 * 832301 * 2
def baseEnd_832301 : Nat := 379884855304758535297621

theorem tailTrace_832301 : CollatzResearch.WordTrace tailWord_832301 prefixEnd_832301 379884855304758535297621 := by
  unfold tailWord_832301
  simp only [CollatzResearch.WordTrace]
  refine ⟨30356511357723097539112757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20237674238482065026075171 30356511357723097539112757)
  ·
    refine ⟨2845922939786540394291821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30356511357723097539112757 2845922939786540394291821)
    ·
      refine ⟨1067221102419952647859433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2845922939786540394291821 1067221102419952647859433)
      ·
        refine ⟨800415826814964485894575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1067221102419952647859433 800415826814964485894575)
        ·
          refine ⟨1200623740222446728841863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800415826814964485894575 1200623740222446728841863)
          ·
            refine ⟨1800935610333670093262795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200623740222446728841863 1800935610333670093262795)
            ·
              refine ⟨2701403415500505139894193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800935610333670093262795 2701403415500505139894193)
              ·
                refine ⟨2026052561625378854920645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701403415500505139894193 2026052561625378854920645)
                ·
                  refine ⟨379884855304758535297621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026052561625378854920645 379884855304758535297621)
                  ·
                    rfl

theorem cell20_832301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_832301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832301 prefixEnd_832301 := by exact prefixLift 832301
  have htrace : WordTrace (prefixWord ++ tailWord_832301) baseStart_832301 baseEnd_832301 := by
    simpa [prefixWord, tailWord_832301, baseEnd_832301] using wordTrace_append hprefix tailTrace_832301
  have hstable : (prefixWord ++ tailWord_832301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832301).length < 2 ^ (prefixWord ++ tailWord_832301).sum := by decide
  have hdescent : baseEnd_832301 < baseStart_832301 := by decide
  rcases family_descends (prefixWord ++ tailWord_832301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832308 : List Nat := [2, 5, 1, 1, 3, 1, 3, 4]
def baseStart_832308 : Nat := 118140960795 + 832308 * 2 ^ 59
def prefixEnd_832308 : Nat := 4983230072969 + 3 ^ 40 * 832308 * 2
def baseEnd_832308 : Nat := 126629350098499207354753

theorem tailTrace_832308 : CollatzResearch.WordTrace tailWord_832308 prefixEnd_832308 126629350098499207354753 := by
  unfold tailWord_832308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15178383334348868867308789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20237844445798491823078385 15178383334348868867308789)
  ·
    refine ⟨1422973437595206456310199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15178383334348868867308789 1422973437595206456310199)
    ·
      refine ⟨2134460156392809684465299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422973437595206456310199 2134460156392809684465299)
      ·
        refine ⟨3201690234589214526697949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134460156392809684465299 3201690234589214526697949)
        ·
          refine ⟨1200633837970955447511731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3201690234589214526697949 1200633837970955447511731)
          ·
            refine ⟨1800950756956433171267597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200633837970955447511731 1800950756956433171267597)
            ·
              refine ⟨675356533858662439225349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1800950756956433171267597 675356533858662439225349)
              ·
                refine ⟨126629350098499207354753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675356533858662439225349 126629350098499207354753)
                ·
                  rfl

theorem cell20_832308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_832308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832308 prefixEnd_832308 := by exact prefixLift 832308
  have htrace : WordTrace (prefixWord ++ tailWord_832308) baseStart_832308 baseEnd_832308 := by
    simpa [prefixWord, tailWord_832308, baseEnd_832308] using wordTrace_append hprefix tailTrace_832308
  have hstable : (prefixWord ++ tailWord_832308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832308).length < 2 ^ (prefixWord ++ tailWord_832308).sum := by decide
  have hdescent : baseEnd_832308 < baseStart_832308 := by decide
  rcases family_descends (prefixWord ++ tailWord_832308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832312 : List Nat := [2, 1, 2, 1, 3, 2, 5, 4]
def baseStart_832312 : Nat := 118140960795 + 832312 * 2 ^ 59
def prefixEnd_832312 : Nat := 4983230072969 + 3 ^ 40 * 832312 * 2
def baseEnd_832312 : Nat := 126629958668163795310303

theorem tailTrace_832312 : CollatzResearch.WordTrace tailWord_832312 prefixEnd_832312 126629958668163795310303 := by
  unfold tailWord_832312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15178456280341623208881595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20237941707122164278508793 15178456280341623208881595)
  ·
    refine ⟨22767684420512434813322393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15178456280341623208881595 22767684420512434813322393)
    ·
      refine ⟨17075763315384326109991795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22767684420512434813322393 17075763315384326109991795)
      ·
        refine ⟨25613644973076489164987693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17075763315384326109991795 25613644973076489164987693)
        ·
          refine ⟨9605116864903683436870385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25613644973076489164987693 9605116864903683436870385)
          ·
            refine ⟨7203837648677762577652789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605116864903683436870385 7203837648677762577652789)
            ·
              refine ⟨675359779563540241654949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7203837648677762577652789 675359779563540241654949)
              ·
                refine ⟨126629958668163795310303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675359779563540241654949 126629958668163795310303)
                ·
                  rfl

theorem cell20_832312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_832312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832312 prefixEnd_832312 := by exact prefixLift 832312
  have htrace : WordTrace (prefixWord ++ tailWord_832312) baseStart_832312 baseEnd_832312 := by
    simpa [prefixWord, tailWord_832312, baseEnd_832312] using wordTrace_append hprefix tailTrace_832312
  have hstable : (prefixWord ++ tailWord_832312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832312).length < 2 ^ (prefixWord ++ tailWord_832312).sum := by decide
  have hdescent : baseEnd_832312 < baseStart_832312 := by decide
  rcases family_descends (prefixWord ++ tailWord_832312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832343 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_832343 : Nat := 118140960795 + 832343 * 2 ^ 59
def prefixEnd_832343 : Nat := 4983230072969 + 3 ^ 40 * 832343 * 2
def baseEnd_832343 : Nat := 379904025249193055897449

theorem tailTrace_832343 : CollatzResearch.WordTrace tailWord_832343 prefixEnd_832343 379904025249193055897449 := by
  unfold tailWord_832343
  simp only [CollatzResearch.WordTrace]
  refine ⟨30358043223570938712141683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20238695482380625808094455 30358043223570938712141683)
  ·
    refine ⟨45537064835356408068212525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30358043223570938712141683 45537064835356408068212525)
    ·
      refine ⟨17076399313258653025579697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45537064835356408068212525 17076399313258653025579697)
      ·
        refine ⟨12807299484943989769184773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17076399313258653025579697 12807299484943989769184773)
        ·
          refine ⟨2401368653426998081722145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12807299484943989769184773 2401368653426998081722145)
          ·
            refine ⟨1801026490070248561291609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401368653426998081722145 1801026490070248561291609)
            ·
              refine ⟨1350769867552686420968707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801026490070248561291609 1350769867552686420968707)
              ·
                refine ⟨2026154801329029631453061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350769867552686420968707 2026154801329029631453061)
                ·
                  refine ⟨379904025249193055897449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026154801329029631453061 379904025249193055897449)
                  ·
                    rfl

theorem cell20_832343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_832343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832343 prefixEnd_832343 := by exact prefixLift 832343
  have htrace : WordTrace (prefixWord ++ tailWord_832343) baseStart_832343 baseEnd_832343 := by
    simpa [prefixWord, tailWord_832343, baseEnd_832343] using wordTrace_append hprefix tailTrace_832343
  have hstable : (prefixWord ++ tailWord_832343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832343).length < 2 ^ (prefixWord ++ tailWord_832343).sum := by decide
  have hdescent : baseEnd_832343 < baseStart_832343 := by decide
  rcases family_descends (prefixWord ++ tailWord_832343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832357 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_832357 : Nat := 118140960795 + 832357 * 2 ^ 59
def prefixEnd_832357 : Nat := 4983230072969 + 3 ^ 40 * 832357 * 2
def baseEnd_832357 : Nat := 379910415230671229430725

theorem tailTrace_832357 : CollatzResearch.WordTrace tailWord_832357 prefixEnd_832357 379910415230671229430725 := by
  unfold tailWord_832357
  simp only [CollatzResearch.WordTrace]
  refine ⟨30358553845520219103151325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20239035897013479402100883 30358553845520219103151325)
  ·
    refine ⟨11384457692070082163681747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30358553845520219103151325 11384457692070082163681747)
    ·
      refine ⟨17076686538105123245522621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11384457692070082163681747 17076686538105123245522621)
      ·
        refine ⟨6403757451789421217070983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17076686538105123245522621 6403757451789421217070983)
        ·
          refine ⟨9605636177684131825606475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403757451789421217070983 9605636177684131825606475)
          ·
            refine ⟨14408454266526197738409713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605636177684131825606475 14408454266526197738409713)
            ·
              refine ⟨10806340699894648303807285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14408454266526197738409713 10806340699894648303807285)
              ·
                refine ⟨1013094440615123278481933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10806340699894648303807285 1013094440615123278481933)
                ·
                  refine ⟨379910415230671229430725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013094440615123278481933 379910415230671229430725)
                  ·
                    rfl

theorem cell20_832357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_832357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832357 prefixEnd_832357 := by exact prefixLift 832357
  have htrace : WordTrace (prefixWord ++ tailWord_832357) baseStart_832357 baseEnd_832357 := by
    simpa [prefixWord, tailWord_832357, baseEnd_832357] using wordTrace_append hprefix tailTrace_832357
  have hstable : (prefixWord ++ tailWord_832357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832357).length < 2 ^ (prefixWord ++ tailWord_832357).sum := by decide
  have hdescent : baseEnd_832357 < baseStart_832357 := by decide
  rcases family_descends (prefixWord ++ tailWord_832357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832364 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_832364 : Nat := 118140960795 + 832364 * 2 ^ 59
def prefixEnd_832364 : Nat := 4983230072969 + 3 ^ 40 * 832364 * 2
def baseEnd_832364 : Nat := 379913610221410316197363

theorem tailTrace_832364 : CollatzResearch.WordTrace tailWord_832364 prefixEnd_832364 379913610221410316197363 := by
  unfold tailWord_832364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179404578247429649328073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20239206104329906199104097 15179404578247429649328073)
  ·
    refine ⟨11384553433685572236996055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15179404578247429649328073 11384553433685572236996055)
    ·
      refine ⟨17076830150528358355494083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11384553433685572236996055 17076830150528358355494083)
      ·
        refine ⟨25615245225792537533241125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17076830150528358355494083 25615245225792537533241125)
        ·
          refine ⟨4802858479836100787482711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25615245225792537533241125 4802858479836100787482711)
          ·
            refine ⟨7204287719754151181224067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802858479836100787482711 7204287719754151181224067)
            ·
              refine ⟨10806431579631226771836101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204287719754151181224067 10806431579631226771836101)
              ·
                refine ⟨2026205921180855019719269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10806431579631226771836101 2026205921180855019719269)
                ·
                  refine ⟨379913610221410316197363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026205921180855019719269 379913610221410316197363)
                  ·
                    rfl

theorem cell20_832364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_832364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832364 prefixEnd_832364 := by exact prefixLift 832364
  have htrace : WordTrace (prefixWord ++ tailWord_832364) baseStart_832364 baseEnd_832364 := by
    simpa [prefixWord, tailWord_832364, baseEnd_832364] using wordTrace_append hprefix tailTrace_832364
  have hstable : (prefixWord ++ tailWord_832364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832364).length < 2 ^ (prefixWord ++ tailWord_832364).sum := by decide
  have hdescent : baseEnd_832364 < baseStart_832364 := by decide
  rcases family_descends (prefixWord ++ tailWord_832364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832374 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_832374 : Nat := 118140960795 + 832374 * 2 ^ 59
def prefixEnd_832374 : Nat := 4983230072969 + 3 ^ 40 * 832374 * 2
def baseEnd_832374 : Nat := 379918174493894725863989

theorem tailTrace_832374 : CollatzResearch.WordTrace tailWord_832374 prefixEnd_832374 379918174493894725863989 := by
  unfold tailWord_832374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897448367903664437907511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20239449257639087337680117 1897448367903664437907511)
  ·
    refine ⟨2846172551855496656861267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1897448367903664437907511 2846172551855496656861267)
    ·
      refine ⟨4269258827783244985291901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2846172551855496656861267 4269258827783244985291901)
      ·
        refine ⟨1600972060418716869484463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4269258827783244985291901 1600972060418716869484463)
        ·
          refine ⟨2401458090628075304226695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600972060418716869484463 2401458090628075304226695)
          ·
            refine ⟨3602187135942112956340043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401458090628075304226695 3602187135942112956340043)
            ·
              refine ⟨5403280703913169434510065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602187135942112956340043 5403280703913169434510065)
              ·
                refine ⟨4052460527934877075882549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403280703913169434510065 4052460527934877075882549)
                ·
                  refine ⟨379918174493894725863989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052460527934877075882549 379918174493894725863989)
                  ·
                    rfl

theorem cell20_832374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_832374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832374 prefixEnd_832374 := by exact prefixLift 832374
  have htrace : WordTrace (prefixWord ++ tailWord_832374) baseStart_832374 baseEnd_832374 := by
    simpa [prefixWord, tailWord_832374, baseEnd_832374] using wordTrace_append hprefix tailTrace_832374
  have hstable : (prefixWord ++ tailWord_832374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832374).length < 2 ^ (prefixWord ++ tailWord_832374).sum := by decide
  have hdescent : baseEnd_832374 < baseStart_832374 := by decide
  rcases family_descends (prefixWord ++ tailWord_832374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832495 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 2]
def baseStart_832495 : Nat := 118140960795 + 832495 * 2 ^ 59
def prefixEnd_832495 : Nat := 4983230072969 + 3 ^ 40 * 832495 * 2
def baseEnd_832495 : Nat := 379973402190956082830161

theorem tailTrace_832495 : CollatzResearch.WordTrace tailWord_832495 prefixEnd_832495 379973402190956082830161 := by
  unfold tailWord_832495
  simp only [CollatzResearch.WordTrace]
  refine ⟨30363587119020268671674939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20242391412680179114449959 30363587119020268671674939)
  ·
    refine ⟨45545380678530403007512409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30363587119020268671674939 45545380678530403007512409)
    ·
      refine ⟨34159035508897802255634307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45545380678530403007512409 34159035508897802255634307)
      ·
        refine ⟨51238553263346703383451461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34159035508897802255634307 51238553263346703383451461)
        ·
          refine ⟨9607228736877506884397149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51238553263346703383451461 9607228736877506884397149)
          ·
            refine ⟨3602710776329065081648931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9607228736877506884397149 3602710776329065081648931)
            ·
              refine ⟨5404066164493597622473397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602710776329065081648931 5404066164493597622473397)
              ·
                refine ⟨506631202921274777106881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5404066164493597622473397 506631202921274777106881)
                ·
                  refine ⟨379973402190956082830161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506631202921274777106881 379973402190956082830161)
                  ·
                    rfl

theorem cell20_832495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 2].length) (baseStart_832495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832495 prefixEnd_832495 := by exact prefixLift 832495
  have htrace : WordTrace (prefixWord ++ tailWord_832495) baseStart_832495 baseEnd_832495 := by
    simpa [prefixWord, tailWord_832495, baseEnd_832495] using wordTrace_append hprefix tailTrace_832495
  have hstable : (prefixWord ++ tailWord_832495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832495).length < 2 ^ (prefixWord ++ tailWord_832495).sum := by decide
  have hdescent : baseEnd_832495 < baseStart_832495 := by decide
  rcases family_descends (prefixWord ++ tailWord_832495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832501 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 3]
def baseStart_832501 : Nat := 118140960795 + 832501 * 2 ^ 59
def prefixEnd_832501 : Nat := 4983230072969 + 3 ^ 40 * 832501 * 2
def baseEnd_832501 : Nat := 379976140754446728630137

theorem tailTrace_832501 : CollatzResearch.WordTrace tailWord_832501 prefixEnd_832501 379976140754446728630137 := by
  unfold tailWord_832501
  simp only [CollatzResearch.WordTrace]
  refine ⟨30363805956998531696393357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20242537304665687797595571 30363805956998531696393357)
  ·
    refine ⟨11386427233874449386147509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30363805956998531696393357 11386427233874449386147509)
    ·
      refine ⟨1067477553175729629951329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11386427233874449386147509 1067477553175729629951329)
      ·
        refine ⟨800608164881797222463497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1067477553175729629951329 800608164881797222463497)
        ·
          refine ⟨600456123661347916847623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800608164881797222463497 600456123661347916847623)
          ·
            refine ⟨900684185492021875271435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600456123661347916847623 900684185492021875271435)
            ·
              refine ⟨1351026278238032812907153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900684185492021875271435 1351026278238032812907153)
              ·
                refine ⟨1013269708678524609680365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351026278238032812907153 1013269708678524609680365)
                ·
                  refine ⟨379976140754446728630137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013269708678524609680365 379976140754446728630137)
                  ·
                    rfl

theorem cell20_832501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_832501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832501 prefixEnd_832501 := by exact prefixLift 832501
  have htrace : WordTrace (prefixWord ++ tailWord_832501) baseStart_832501 baseEnd_832501 := by
    simpa [prefixWord, tailWord_832501, baseEnd_832501] using wordTrace_append hprefix tailTrace_832501
  have hstable : (prefixWord ++ tailWord_832501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832501).length < 2 ^ (prefixWord ++ tailWord_832501).sum := by decide
  have hdescent : baseEnd_832501 < baseStart_832501 := by decide
  rcases family_descends (prefixWord ++ tailWord_832501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832502 : List Nat := [5, 1, 1, 1, 3, 2, 7]
def baseStart_832502 : Nat := 118140960795 + 832502 * 2 ^ 59
def prefixEnd_832502 : Nat := 4983230072969 + 3 ^ 40 * 832502 * 2
def baseEnd_832502 : Nat := 42219621909077241066311

theorem tailTrace_832502 : CollatzResearch.WordTrace tailWord_832502 prefixEnd_832502 42219621909077241066311 := by
  unfold tailWord_832502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897740151874681804198735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20242561619996605911453173 1897740151874681804198735)
  ·
    refine ⟨2846610227812022706298103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1897740151874681804198735 2846610227812022706298103)
    ·
      refine ⟨4269915341718034059447155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2846610227812022706298103 4269915341718034059447155)
      ·
        refine ⟨6404873012577051089170733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4269915341718034059447155 6404873012577051089170733)
        ·
          refine ⟨2401827379716394158439025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6404873012577051089170733 2401827379716394158439025)
          ·
            refine ⟨1801370534787295618829269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401827379716394158439025 1801370534787295618829269)
            ·
              refine ⟨42219621909077241066311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1801370534787295618829269 42219621909077241066311)
              ·
                rfl

theorem cell20_832502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_832502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832502 prefixEnd_832502 := by exact prefixLift 832502
  have htrace : WordTrace (prefixWord ++ tailWord_832502) baseStart_832502 baseEnd_832502 := by
    simpa [prefixWord, tailWord_832502, baseEnd_832502] using wordTrace_append hprefix tailTrace_832502
  have hstable : (prefixWord ++ tailWord_832502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832502).length < 2 ^ (prefixWord ++ tailWord_832502).sum := by decide
  have hdescent : baseEnd_832502 < baseStart_832502 := by decide
  rcases family_descends (prefixWord ++ tailWord_832502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832540 : List Nat := [2, 2, 3, 1, 4, 1, 1, 6]
def baseStart_832540 : Nat := 118140960795 + 832540 * 2 ^ 59
def prefixEnd_832540 : Nat := 4983230072969 + 3 ^ 40 * 832540 * 2
def baseEnd_832540 : Nat := 126664647139045308776659

theorem tailTrace_832540 : CollatzResearch.WordTrace tailWord_832540 prefixEnd_832540 126664647139045308776659 := by
  unfold tailWord_832540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182614201928620678531537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20243485602571494238042049 15182614201928620678531537)
  ·
    refine ⟨11386960651446465508898653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15182614201928620678531537 11386960651446465508898653)
    ·
      refine ⟨4270110244292424565836995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11386960651446465508898653 4270110244292424565836995)
      ·
        refine ⟨6405165366438636848755493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270110244292424565836995 6405165366438636848755493)
        ·
          refine ⟨1200968506207244409141655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6405165366438636848755493 1200968506207244409141655)
          ·
            refine ⟨1801452759310866613712483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200968506207244409141655 1801452759310866613712483)
            ·
              refine ⟨2702179138966299920568725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801452759310866613712483 2702179138966299920568725)
              ·
                refine ⟨126664647139045308776659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2702179138966299920568725 126664647139045308776659)
                ·
                  rfl

theorem cell20_832540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_832540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832540 prefixEnd_832540 := by exact prefixLift 832540
  have htrace : WordTrace (prefixWord ++ tailWord_832540) baseStart_832540 baseEnd_832540 := by
    simpa [prefixWord, tailWord_832540, baseEnd_832540] using wordTrace_append hprefix tailTrace_832540
  have hstable : (prefixWord ++ tailWord_832540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832540).length < 2 ^ (prefixWord ++ tailWord_832540).sum := by decide
  have hdescent : baseEnd_832540 < baseStart_832540 := by decide
  rcases family_descends (prefixWord ++ tailWord_832540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832564 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_832564 : Nat := 118140960795 + 832564 * 2 ^ 59
def prefixEnd_832564 : Nat := 4983230072969 + 3 ^ 40 * 832564 * 2
def baseEnd_832564 : Nat := 380004895671098509529879

theorem tailTrace_832564 : CollatzResearch.WordTrace tailWord_832564 prefixEnd_832564 380004895671098509529879 := by
  unfold tailWord_832564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183051877885146727968373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20244069170513528970624497 15183051877885146727968373)
  ·
    refine ⟨1423411113551732505747035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15183051877885146727968373 1423411113551732505747035)
    ·
      refine ⟨2135116670327598758620553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423411113551732505747035 2135116670327598758620553)
      ·
        refine ⟨1601337502745699068965415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2135116670327598758620553 1601337502745699068965415)
        ·
          refine ⟨2402006254118548603448123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601337502745699068965415 2402006254118548603448123)
          ·
            refine ⟨3603009381177822905172185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402006254118548603448123 3603009381177822905172185)
            ·
              refine ⟨2702257035883367178879139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603009381177822905172185 2702257035883367178879139)
              ·
                refine ⟨4053385553825050768318709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702257035883367178879139 4053385553825050768318709)
                ·
                  refine ⟨380004895671098509529879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053385553825050768318709 380004895671098509529879)
                  ·
                    rfl

theorem cell20_832564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_832564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832564 prefixEnd_832564 := by exact prefixLift 832564
  have htrace : WordTrace (prefixWord ++ tailWord_832564) baseStart_832564 baseEnd_832564 := by
    simpa [prefixWord, tailWord_832564, baseEnd_832564] using wordTrace_append hprefix tailTrace_832564
  have hstable : (prefixWord ++ tailWord_832564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832564).length < 2 ^ (prefixWord ++ tailWord_832564).sum := by decide
  have hdescent : baseEnd_832564 < baseStart_832564 := by decide
  rcases family_descends (prefixWord ++ tailWord_832564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832616 : List Nat := [2, 1, 4, 4, 1, 8]
def baseStart_832616 : Nat := 118140960795 + 832616 * 2 ^ 59
def prefixEnd_832616 : Nat := 4983230072969 + 3 ^ 40 * 832616 * 2
def baseEnd_832616 : Nat := 14075134440296942214679

theorem tailTrace_832616 : CollatzResearch.WordTrace tailWord_832616 prefixEnd_832616 14075134440296942214679 := by
  unfold tailWord_832616
  simp only [CollatzResearch.WordTrace]
  refine ⟨15184000175790953168414851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20245333567721270891219801 15184000175790953168414851)
  ·
    refine ⟨22776000263686429752622277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15184000175790953168414851 22776000263686429752622277)
    ·
      refine ⟨4270500049441205578616677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22776000263686429752622277 4270500049441205578616677)
      ·
        refine ⟨800718759270226045990627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4270500049441205578616677 800718759270226045990627)
        ·
          refine ⟨1201078138905339068985941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800718759270226045990627 1201078138905339068985941)
          ·
            refine ⟨14075134440296942214679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1201078138905339068985941 14075134440296942214679)
            ·
              rfl

theorem cell20_832616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 8].length) (baseStart_832616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832616 prefixEnd_832616 := by exact prefixLift 832616
  have htrace : WordTrace (prefixWord ++ tailWord_832616) baseStart_832616 baseEnd_832616 := by
    simpa [prefixWord, tailWord_832616, baseEnd_832616] using wordTrace_append hprefix tailTrace_832616
  have hstable : (prefixWord ++ tailWord_832616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832616).length < 2 ^ (prefixWord ++ tailWord_832616).sum := by decide
  have hdescent : baseEnd_832616 < baseStart_832616 := by decide
  rcases family_descends (prefixWord ++ tailWord_832616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832623 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_832623 : Nat := 118140960795 + 832623 * 2 ^ 59
def prefixEnd_832623 : Nat := 4983230072969 + 3 ^ 40 * 832623 * 2
def baseEnd_832623 : Nat := 380031824878756526562971

theorem tailTrace_832623 : CollatzResearch.WordTrace tailWord_832623 prefixEnd_832623 380031824878756526562971 := by
  unfold tailWord_832623
  simp only [CollatzResearch.WordTrace]
  refine ⟨30368255662556546532334523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20245503775037697688223015 30368255662556546532334523)
  ·
    refine ⟨45552383493834819798501785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30368255662556546532334523 45552383493834819798501785)
    ·
      refine ⟨34164287620376114848876339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45552383493834819798501785 34164287620376114848876339)
      ·
        refine ⟨51246431430564172273314509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34164287620376114848876339 51246431430564172273314509)
        ·
          refine ⟨19217411786461564602492941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51246431430564172273314509 19217411786461564602492941)
          ·
            refine ⟨7206529419923086725934853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19217411786461564602492941 7206529419923086725934853)
            ·
              refine ⟨1351224266235578761112785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7206529419923086725934853 1351224266235578761112785)
              ·
                refine ⟨1013418199676684070834589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351224266235578761112785 1013418199676684070834589)
                ·
                  refine ⟨380031824878756526562971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013418199676684070834589 380031824878756526562971)
                  ·
                    rfl

theorem cell20_832623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_832623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832623 prefixEnd_832623 := by exact prefixLift 832623
  have htrace : WordTrace (prefixWord ++ tailWord_832623) baseStart_832623 baseEnd_832623 := by
    simpa [prefixWord, tailWord_832623, baseEnd_832623] using wordTrace_append hprefix tailTrace_832623
  have hstable : (prefixWord ++ tailWord_832623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832623).length < 2 ^ (prefixWord ++ tailWord_832623).sum := by decide
  have hdescent : baseEnd_832623 < baseStart_832623 := by decide
  rcases family_descends (prefixWord ++ tailWord_832623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832633 : List Nat := [1, 2, 1, 3, 6, 1, 1, 5]
def baseStart_832633 : Nat := 118140960795 + 832633 * 2 ^ 59
def prefixEnd_832633 : Nat := 4983230072969 + 3 ^ 40 * 832633 * 2
def baseEnd_832633 : Nat := 126678796383746978743199

theorem tailTrace_832633 : CollatzResearch.WordTrace tailWord_832633 prefixEnd_832633 126678796383746978743199 := by
  unfold tailWord_832633
  simp only [CollatzResearch.WordTrace]
  refine ⟨30368620392520318240198553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20245746928346878826799035 30368620392520318240198553)
  ·
    refine ⟨22776465294390238680148915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30368620392520318240198553 22776465294390238680148915)
    ·
      refine ⟨34164697941585358020223373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22776465294390238680148915 34164697941585358020223373)
      ·
        refine ⟨12811761728094509257583765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34164697941585358020223373 12811761728094509257583765)
        ·
          refine ⟨600551331004430121449239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12811761728094509257583765 600551331004430121449239)
          ·
            refine ⟨900826996506645182173859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600551331004430121449239 900826996506645182173859)
            ·
              refine ⟨1351240494759967773260789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900826996506645182173859 1351240494759967773260789)
              ·
                refine ⟨126678796383746978743199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351240494759967773260789 126678796383746978743199)
                ·
                  rfl

theorem cell20_832633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].length) (baseStart_832633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832633 prefixEnd_832633 := by exact prefixLift 832633
  have htrace : WordTrace (prefixWord ++ tailWord_832633) baseStart_832633 baseEnd_832633 := by
    simpa [prefixWord, tailWord_832633, baseEnd_832633] using wordTrace_append hprefix tailTrace_832633
  have hstable : (prefixWord ++ tailWord_832633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832633).length < 2 ^ (prefixWord ++ tailWord_832633).sum := by decide
  have hdescent : baseEnd_832633 < baseStart_832633 := by decide
  rcases family_descends (prefixWord ++ tailWord_832633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832664 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 2]
def baseStart_832664 : Nat := 118140960795 + 832664 * 2 ^ 59
def prefixEnd_832664 : Nat := 4983230072969 + 3 ^ 40 * 832664 * 2
def baseEnd_832664 : Nat := 380050538395942606196137

theorem tailTrace_832664 : CollatzResearch.WordTrace tailWord_832664 prefixEnd_832664 380050538395942606196137 := by
  unfold tailWord_832664
  simp only [CollatzResearch.WordTrace]
  refine ⟨15184875527704005267288523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20246500703605340356384697 15184875527704005267288523)
  ·
    refine ⟨22777313291556007900932785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15184875527704005267288523 22777313291556007900932785)
    ·
      refine ⟨17082984968667005925699589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22777313291556007900932785 17082984968667005925699589)
      ·
        refine ⟨3203059681625063611068673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17082984968667005925699589 3203059681625063611068673)
        ·
          refine ⟨2402294761218797708301505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3203059681625063611068673 2402294761218797708301505)
          ·
            refine ⟨1801721070914098281226129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402294761218797708301505 1801721070914098281226129)
            ·
              refine ⟨1351290803185573710919597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801721070914098281226129 1351290803185573710919597)
              ·
                refine ⟨506734051194590141594849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1351290803185573710919597 506734051194590141594849)
                ·
                  refine ⟨380050538395942606196137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506734051194590141594849 380050538395942606196137)
                  ·
                    rfl

theorem cell20_832664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_832664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832664 prefixEnd_832664 := by exact prefixLift 832664
  have htrace : WordTrace (prefixWord ++ tailWord_832664) baseStart_832664 baseEnd_832664 := by
    simpa [prefixWord, tailWord_832664, baseEnd_832664] using wordTrace_append hprefix tailTrace_832664
  have hstable : (prefixWord ++ tailWord_832664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832664).length < 2 ^ (prefixWord ++ tailWord_832664).sum := by decide
  have hdescent : baseEnd_832664 < baseStart_832664 := by decide
  rcases family_descends (prefixWord ++ tailWord_832664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832674 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_832674 : Nat := 118140960795 + 832674 * 2 ^ 59
def prefixEnd_832674 : Nat := 4983230072969 + 3 ^ 40 * 832674 * 2
def baseEnd_832674 : Nat := 380055102668427015862763

theorem tailTrace_832674 : CollatzResearch.WordTrace tailWord_832674 prefixEnd_832674 380055102668427015862763 := by
  unfold tailWord_832674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592528946342945560610269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20246743856914521494960717 7592528946342945560610269)
  ·
    refine ⟨2847198354878604585228851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7592528946342945560610269 2847198354878604585228851)
    ·
      refine ⟨4270797532317906877843277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847198354878604585228851 4270797532317906877843277)
      ·
        refine ⟨1601549074619215079191229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4270797532317906877843277 1601549074619215079191229)
        ·
          refine ⟨600580902982205654696711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1601549074619215079191229 600580902982205654696711)
          ·
            refine ⟨900871354473308482045067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600580902982205654696711 900871354473308482045067)
            ·
              refine ⟨1351307031709962723067601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900871354473308482045067 1351307031709962723067601)
              ·
                refine ⟨1013480273782472042300701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351307031709962723067601 1013480273782472042300701)
                ·
                  refine ⟨380055102668427015862763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013480273782472042300701 380055102668427015862763)
                  ·
                    rfl

theorem cell20_832674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_832674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832674 prefixEnd_832674 := by exact prefixLift 832674
  have htrace : WordTrace (prefixWord ++ tailWord_832674) baseStart_832674 baseEnd_832674 := by
    simpa [prefixWord, tailWord_832674, baseEnd_832674] using wordTrace_append hprefix tailTrace_832674
  have hstable : (prefixWord ++ tailWord_832674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832674).length < 2 ^ (prefixWord ++ tailWord_832674).sum := by decide
  have hdescent : baseEnd_832674 < baseStart_832674 := by decide
  rcases family_descends (prefixWord ++ tailWord_832674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832726 : List Nat := [5, 2, 1, 2, 3, 1, 6]
def baseStart_832726 : Nat := 118140960795 + 832726 * 2 ^ 59
def prefixEnd_832726 : Nat := 4983230072969 + 3 ^ 40 * 832726 * 2
def baseEnd_832726 : Nat := 42230981876149549569913

theorem tailTrace_832726 : CollatzResearch.WordTrace tailWord_832726 prefixEnd_832726 42230981876149549569913 := by
  unfold tailWord_832726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898250773823962195208377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20248008254122263415556021 1898250773823962195208377)
  ·
    refine ⟨1423688080367971646406283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1898250773823962195208377 1423688080367971646406283)
    ·
      refine ⟨2135532120551957469609425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423688080367971646406283 2135532120551957469609425)
      ·
        refine ⟨1601649090413968102207069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2135532120551957469609425 1601649090413968102207069)
        ·
          refine ⟨600618408905238038327651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1601649090413968102207069 600618408905238038327651)
          ·
            refine ⟨900927613357857057491477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600618408905238038327651 900927613357857057491477)
            ·
              refine ⟨42230981876149549569913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 900927613357857057491477 42230981876149549569913)
              ·
                rfl

theorem cell20_832726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 6].length) (baseStart_832726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832726 prefixEnd_832726 := by exact prefixLift 832726
  have htrace : WordTrace (prefixWord ++ tailWord_832726) baseStart_832726 baseEnd_832726 := by
    simpa [prefixWord, tailWord_832726, baseEnd_832726] using wordTrace_append hprefix tailTrace_832726
  have hstable : (prefixWord ++ tailWord_832726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832726).length < 2 ^ (prefixWord ++ tailWord_832726).sum := by decide
  have hdescent : baseEnd_832726 < baseStart_832726 := by decide
  rcases family_descends (prefixWord ++ tailWord_832726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832727 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_832727 : Nat := 118140960795 + 832727 * 2 ^ 59
def prefixEnd_832727 : Nat := 4983230072969 + 3 ^ 40 * 832727 * 2
def baseEnd_832727 : Nat := 380079293312594387095879

theorem tailTrace_832727 : CollatzResearch.WordTrace tailWord_832727 prefixEnd_832727 380079293312594387095879 := by
  unfold tailWord_832727
  simp only [CollatzResearch.WordTrace]
  refine ⟨30372048854179772294120435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20248032569453181529413623 30372048854179772294120435)
  ·
    refine ⟨45558073281269658441180653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30372048854179772294120435 45558073281269658441180653)
    ·
      refine ⟨17084277480476121915442745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45558073281269658441180653 17084277480476121915442745)
      ·
        refine ⟨12813208110357091436582059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17084277480476121915442745 12813208110357091436582059)
        ·
          refine ⟨19219812165535637154873089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12813208110357091436582059 19219812165535637154873089)
          ·
            refine ⟨14414859124151727866154817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19219812165535637154873089 14414859124151727866154817)
            ·
              refine ⟨10811144343113795899616113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14414859124151727866154817 10811144343113795899616113)
              ·
                refine ⟨8108358257335346924712085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10811144343113795899616113 8108358257335346924712085)
                ·
                  refine ⟨380079293312594387095879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8108358257335346924712085 380079293312594387095879)
                  ·
                    rfl

theorem cell20_832727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_832727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832727 prefixEnd_832727 := by exact prefixLift 832727
  have htrace : WordTrace (prefixWord ++ tailWord_832727) baseStart_832727 baseEnd_832727 := by
    simpa [prefixWord, tailWord_832727, baseEnd_832727] using wordTrace_append hprefix tailTrace_832727
  have hstable : (prefixWord ++ tailWord_832727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832727).length < 2 ^ (prefixWord ++ tailWord_832727).sum := by decide
  have hdescent : baseEnd_832727 < baseStart_832727 := by decide
  rcases family_descends (prefixWord ++ tailWord_832727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832754 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_832754 : Nat := 118140960795 + 832754 * 2 ^ 59
def prefixEnd_832754 : Nat := 4983230072969 + 3 ^ 40 * 832754 * 2
def baseEnd_832754 : Nat := 380091616848302293195769

theorem tailTrace_832754 : CollatzResearch.WordTrace tailWord_832754 prefixEnd_832754 380091616848302293195769 := by
  unfold tailWord_832754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593258406270488976338329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20248689083387970603568877 7593258406270488976338329)
  ·
    refine ⟨5694943804702866732253747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7593258406270488976338329 5694943804702866732253747)
    ·
      refine ⟨8542415707054300098380621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694943804702866732253747 8542415707054300098380621)
      ·
        refine ⟨3203405890145362536892733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8542415707054300098380621 3203405890145362536892733)
        ·
          refine ⟨1201277208804510951334775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3203405890145362536892733 1201277208804510951334775)
          ·
            refine ⟨1801915813206766427002163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201277208804510951334775 1801915813206766427002163)
            ·
              refine ⟨2702873719810149640503245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801915813206766427002163 2702873719810149640503245)
              ·
                refine ⟨1013577644928806115188717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2702873719810149640503245 1013577644928806115188717)
                ·
                  refine ⟨380091616848302293195769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013577644928806115188717 380091616848302293195769)
                  ·
                    rfl

theorem cell20_832754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_832754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832754 prefixEnd_832754 := by exact prefixLift 832754
  have htrace : WordTrace (prefixWord ++ tailWord_832754) baseStart_832754 baseEnd_832754 := by
    simpa [prefixWord, tailWord_832754, baseEnd_832754] using wordTrace_append hprefix tailTrace_832754
  have hstable : (prefixWord ++ tailWord_832754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832754).length < 2 ^ (prefixWord ++ tailWord_832754).sum := by decide
  have hdescent : baseEnd_832754 < baseStart_832754 := by decide
  rcases family_descends (prefixWord ++ tailWord_832754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832796 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_832796 : Nat := 118140960795 + 832796 * 2 ^ 59
def prefixEnd_832796 : Nat := 4983230072969 + 3 ^ 40 * 832796 * 2
def baseEnd_832796 : Nat := 380110786792736813795597

theorem tailTrace_832796 : CollatzResearch.WordTrace tailWord_832796 prefixEnd_832796 380110786792736813795597 := by
  unfold tailWord_832796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15187282745464898539191121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20249710327286531385588161 15187282745464898539191121)
  ·
    refine ⟨11390462059098673904393341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15187282745464898539191121 11390462059098673904393341)
    ·
      refine ⟨4271423272162002714147503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11390462059098673904393341 4271423272162002714147503)
      ·
        refine ⟨6407134908243004071221255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271423272162002714147503 6407134908243004071221255)
        ·
          refine ⟨9610702362364506106831883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407134908243004071221255 9610702362364506106831883)
          ·
            refine ⟨14416053543546759160247825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610702362364506106831883 14416053543546759160247825)
            ·
              refine ⟨10812040157660069370185869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14416053543546759160247825 10812040157660069370185869)
              ·
                refine ⟨4054515059122526013819701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10812040157660069370185869 4054515059122526013819701)
                ·
                  refine ⟨380110786792736813795597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4054515059122526013819701 380110786792736813795597)
                  ·
                    rfl

theorem cell20_832796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_832796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832796 prefixEnd_832796 := by exact prefixLift 832796
  have htrace : WordTrace (prefixWord ++ tailWord_832796) baseStart_832796 baseEnd_832796 := by
    simpa [prefixWord, tailWord_832796, baseEnd_832796] using wordTrace_append hprefix tailTrace_832796
  have hstable : (prefixWord ++ tailWord_832796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832796).length < 2 ^ (prefixWord ++ tailWord_832796).sum := by decide
  have hdescent : baseEnd_832796 < baseStart_832796 := by decide
  rcases family_descends (prefixWord ++ tailWord_832796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832848 : List Nat := [2, 1, 1, 1, 1, 5, 9]
def baseStart_832848 : Nat := 118140960795 + 832848 * 2 ^ 59
def prefixEnd_832848 : Nat := 4983230072969 + 3 ^ 40 * 832848 * 2
def baseEnd_832848 : Nat := 42237169001072860451339

theorem tailTrace_832848 : CollatzResearch.WordTrace tailWord_832848 prefixEnd_832848 42237169001072860451339 := by
  unfold tailWord_832848
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188231043370704979637599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20250974724494273306183465 15188231043370704979637599)
  ·
    refine ⟨22782346565056057469456399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15188231043370704979637599 22782346565056057469456399)
    ·
      refine ⟨34173519847584086204184599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22782346565056057469456399 34173519847584086204184599)
      ·
        refine ⟨51260279771376129306276899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34173519847584086204184599 51260279771376129306276899)
        ·
          refine ⟨76890419657064193959415349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51260279771376129306276899 76890419657064193959415349)
          ·
            refine ⟨7208476842849768183695189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76890419657064193959415349 7208476842849768183695189)
            ·
              refine ⟨42237169001072860451339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7208476842849768183695189 42237169001072860451339)
              ·
                rfl

theorem cell20_832848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_832848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832848 prefixEnd_832848 := by exact prefixLift 832848
  have htrace : WordTrace (prefixWord ++ tailWord_832848) baseStart_832848 baseEnd_832848 := by
    simpa [prefixWord, tailWord_832848, baseEnd_832848] using wordTrace_append hprefix tailTrace_832848
  have hstable : (prefixWord ++ tailWord_832848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832848).length < 2 ^ (prefixWord ++ tailWord_832848).sum := by decide
  have hdescent : baseEnd_832848 < baseStart_832848 := by decide
  rcases family_descends (prefixWord ++ tailWord_832848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832868 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_832868 : Nat := 118140960795 + 832868 * 2 ^ 59
def prefixEnd_832868 : Nat := 4983230072969 + 3 ^ 40 * 832868 * 2
def baseEnd_832868 : Nat := 380143649554624563395303

theorem tailTrace_832868 : CollatzResearch.WordTrace tailWord_832868 prefixEnd_832868 380143649554624563395303 := by
  unfold tailWord_832868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188595773334476687501629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20251461031112635583335505 15188595773334476687501629)
  ·
    refine ⟨5695723415000428757813111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15188595773334476687501629 5695723415000428757813111)
    ·
      refine ⟨8543585122500643136719667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695723415000428757813111 8543585122500643136719667)
      ·
        refine ⟨12815377683750964705079501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8543585122500643136719667 12815377683750964705079501)
        ·
          refine ⟨4805766631406611764404813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12815377683750964705079501 4805766631406611764404813)
          ·
            refine ⟨1802162486777479411651805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4805766631406611764404813 1802162486777479411651805)
            ·
              refine ⟨675810932541554779369427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1802162486777479411651805 675810932541554779369427)
              ·
                refine ⟨1013716398812332169054141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675810932541554779369427 1013716398812332169054141)
                ·
                  refine ⟨380143649554624563395303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013716398812332169054141 380143649554624563395303)
                  ·
                    rfl

theorem cell20_832868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_832868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832868 prefixEnd_832868 := by exact prefixLift 832868
  have htrace : WordTrace (prefixWord ++ tailWord_832868) baseStart_832868 baseEnd_832868 := by
    simpa [prefixWord, tailWord_832868, baseEnd_832868] using wordTrace_append hprefix tailTrace_832868
  have hstable : (prefixWord ++ tailWord_832868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832868).length < 2 ^ (prefixWord ++ tailWord_832868).sum := by decide
  have hdescent : baseEnd_832868 < baseStart_832868 := by decide
  rcases family_descends (prefixWord ++ tailWord_832868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832878 : List Nat := [4, 1, 2, 4, 1, 2, 2, 4]
def baseStart_832878 : Nat := 118140960795 + 832878 * 2 ^ 59
def prefixEnd_832878 : Nat := 4983230072969 + 3 ^ 40 * 832878 * 2
def baseEnd_832878 : Nat := 126716071275702991020643

theorem tailTrace_832878 : CollatzResearch.WordTrace tailWord_832878 prefixEnd_832878 126716071275702991020643 := by
  unfold tailWord_832878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797194534579090635358411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20251704184421816721911525 3797194534579090635358411)
  ·
    refine ⟨5695791801868635953037617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3797194534579090635358411 5695791801868635953037617)
    ·
      refine ⟨4271843851401476964778213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5695791801868635953037617 4271843851401476964778213)
      ·
        refine ⟨800970722137776930895915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4271843851401476964778213 800970722137776930895915)
        ·
          refine ⟨1201456083206665396343873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800970722137776930895915 1201456083206665396343873)
          ·
            refine ⟨901092062404999047257905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201456083206665396343873 901092062404999047257905)
            ·
              refine ⟨675819046803749285443429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901092062404999047257905 675819046803749285443429)
              ·
                refine ⟨126716071275702991020643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675819046803749285443429 126716071275702991020643)
                ·
                  rfl

theorem cell20_832878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_832878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832878 prefixEnd_832878 := by exact prefixLift 832878
  have htrace : WordTrace (prefixWord ++ tailWord_832878) baseStart_832878 baseEnd_832878 := by
    simpa [prefixWord, tailWord_832878, baseEnd_832878] using wordTrace_append hprefix tailTrace_832878
  have hstable : (prefixWord ++ tailWord_832878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832878).length < 2 ^ (prefixWord ++ tailWord_832878).sum := by decide
  have hdescent : baseEnd_832878 < baseStart_832878 := by decide
  rcases family_descends (prefixWord ++ tailWord_832878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832879 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_832879 : Nat := 118140960795 + 832879 * 2 ^ 59
def prefixEnd_832879 : Nat := 4983230072969 + 3 ^ 40 * 832879 * 2
def baseEnd_832879 : Nat := 380148670254357414028591

theorem tailTrace_832879 : CollatzResearch.WordTrace tailWord_832879 prefixEnd_832879 380148670254357414028591 := by
  unfold tailWord_832879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30377592749629102253653691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20251728499752734835769127 30377592749629102253653691)
  ·
    refine ⟨45566389124443653380480537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30377592749629102253653691 45566389124443653380480537)
    ·
      refine ⟨34174791843332740035360403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45566389124443653380480537 34174791843332740035360403)
      ·
        refine ⟨51262187764999110053040605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34174791843332740035360403 51262187764999110053040605)
        ·
          refine ⟨19223320411874666269890227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51262187764999110053040605 19223320411874666269890227)
          ·
            refine ⟨28834980617811999404835341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19223320411874666269890227 28834980617811999404835341)
            ·
              refine ⟨10813117731679499776813253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28834980617811999404835341 10813117731679499776813253)
              ·
                refine ⟨2027459574689906208152485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10813117731679499776813253 2027459574689906208152485)
                ·
                  refine ⟨380148670254357414028591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027459574689906208152485 380148670254357414028591)
                  ·
                    rfl

theorem cell20_832879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_832879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832879 prefixEnd_832879 := by exact prefixLift 832879
  have htrace : WordTrace (prefixWord ++ tailWord_832879) baseStart_832879 baseEnd_832879 := by
    simpa [prefixWord, tailWord_832879, baseEnd_832879] using wordTrace_append hprefix tailTrace_832879
  have hstable : (prefixWord ++ tailWord_832879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832879).length < 2 ^ (prefixWord ++ tailWord_832879).sum := by decide
  have hdescent : baseEnd_832879 < baseStart_832879 := by decide
  rcases family_descends (prefixWord ++ tailWord_832879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832903 : List Nat := [1, 1, 4, 2, 2, 4, 6]
def baseStart_832903 : Nat := 118140960795 + 832903 * 2 ^ 59
def prefixEnd_832903 : Nat := 4983230072969 + 3 ^ 40 * 832903 * 2
def baseEnd_832903 : Nat := 42239958278702221914277

theorem tailTrace_832903 : CollatzResearch.WordTrace tailWord_832903 prefixEnd_832903 42239958278702221914277 := by
  unfold tailWord_832903
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378468101542154352527363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20252312067694769568351575 30378468101542154352527363)
  ·
    refine ⟨45567702152313231528791045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30378468101542154352527363 45567702152313231528791045)
    ·
      refine ⟨8543944153558730911648321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45567702152313231528791045 8543944153558730911648321)
      ·
        refine ⟨6407958115169048183736241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8543944153558730911648321 6407958115169048183736241)
        ·
          refine ⟨4805968586376786137802181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407958115169048183736241 4805968586376786137802181)
          ·
            refine ⟨901119109945647400837909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4805968586376786137802181 901119109945647400837909)
            ·
              refine ⟨42239958278702221914277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 901119109945647400837909 42239958278702221914277)
              ·
                rfl

theorem cell20_832903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_832903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832903 prefixEnd_832903 := by exact prefixLift 832903
  have htrace : WordTrace (prefixWord ++ tailWord_832903) baseStart_832903 baseEnd_832903 := by
    simpa [prefixWord, tailWord_832903, baseEnd_832903] using wordTrace_append hprefix tailTrace_832903
  have hstable : (prefixWord ++ tailWord_832903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832903).length < 2 ^ (prefixWord ++ tailWord_832903).sum := by decide
  have hdescent : baseEnd_832903 < baseStart_832903 := by decide
  rcases family_descends (prefixWord ++ tailWord_832903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832920 : List Nat := [2, 1, 2, 5, 2, 1, 2, 5]
def baseStart_832920 : Nat := 118140960795 + 832920 * 2 ^ 59
def prefixEnd_832920 : Nat := 4983230072969 + 3 ^ 40 * 832920 * 2
def baseEnd_832920 : Nat := 126722461257181164553919

theorem tailTrace_832920 : CollatzResearch.WordTrace tailWord_832920 prefixEnd_832920 126722461257181164553919 := by
  unfold tailWord_832920
  simp only [CollatzResearch.WordTrace]
  refine ⟨15189544071240283127948107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20252725428320377503930809 15189544071240283127948107)
  ·
    refine ⟨22784316106860424691922161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15189544071240283127948107 22784316106860424691922161)
    ·
      refine ⟨17088237080145318518941621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22784316106860424691922161 17088237080145318518941621)
      ·
        refine ⟨1602022226263623611150777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17088237080145318518941621 1602022226263623611150777)
        ·
          refine ⟨1201516669697717708363083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1602022226263623611150777 1201516669697717708363083)
          ·
            refine ⟨1802275004546576562544625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201516669697717708363083 1802275004546576562544625)
            ·
              refine ⟨1351706253409932421908469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1802275004546576562544625 1351706253409932421908469)
              ·
                refine ⟨126722461257181164553919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351706253409932421908469 126722461257181164553919)
                ·
                  rfl

theorem cell20_832920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_832920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832920 prefixEnd_832920 := by exact prefixLift 832920
  have htrace : WordTrace (prefixWord ++ tailWord_832920) baseStart_832920 baseEnd_832920 := by
    simpa [prefixWord, tailWord_832920, baseEnd_832920] using wordTrace_append hprefix tailTrace_832920
  have hstable : (prefixWord ++ tailWord_832920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832920).length < 2 ^ (prefixWord ++ tailWord_832920).sum := by decide
  have hdescent : baseEnd_832920 < baseStart_832920 := by decide
  rcases family_descends (prefixWord ++ tailWord_832920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832927 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_832927 : Nat := 118140960795 + 832927 * 2 ^ 59
def prefixEnd_832927 : Nat := 4983230072969 + 3 ^ 40 * 832927 * 2
def baseEnd_832927 : Nat := 380170578762282580428395

theorem tailTrace_832927 : CollatzResearch.WordTrace tailWord_832927 prefixEnd_832927 380170578762282580428395 := by
  unfold tailWord_832927
  simp only [CollatzResearch.WordTrace]
  refine ⟨30379343453455206451401035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20252895635636804300934023 30379343453455206451401035)
  ·
    refine ⟨45569015180182809677101553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30379343453455206451401035 45569015180182809677101553)
    ·
      refine ⟨34176761385137107257826165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45569015180182809677101553 34176761385137107257826165)
      ·
        refine ⟨3204071379856603805421203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34176761385137107257826165 3204071379856603805421203)
        ·
          refine ⟨4806107069784905708131805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204071379856603805421203 4806107069784905708131805)
          ·
            refine ⟨1802290151169339640549427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4806107069784905708131805 1802290151169339640549427)
            ·
              refine ⟨2703435226754009460824141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802290151169339640549427 2703435226754009460824141)
              ·
                refine ⟨1013788210032753547809053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2703435226754009460824141 1013788210032753547809053)
                ·
                  refine ⟨380170578762282580428395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013788210032753547809053 380170578762282580428395)
                  ·
                    rfl

theorem cell20_832927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_832927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832927 prefixEnd_832927 := by exact prefixLift 832927
  have htrace : WordTrace (prefixWord ++ tailWord_832927) baseStart_832927 baseEnd_832927 := by
    simpa [prefixWord, tailWord_832927, baseEnd_832927] using wordTrace_append hprefix tailTrace_832927
  have hstable : (prefixWord ++ tailWord_832927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832927).length < 2 ^ (prefixWord ++ tailWord_832927).sum := by decide
  have hdescent : baseEnd_832927 < baseStart_832927 := by decide
  rcases family_descends (prefixWord ++ tailWord_832927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832982 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_832982 : Nat := 118140960795 + 832982 * 2 ^ 59
def prefixEnd_832982 : Nat := 4983230072969 + 3 ^ 40 * 832982 * 2
def baseEnd_832982 : Nat := 380195682260946833594837

theorem tailTrace_832982 : CollatzResearch.WordTrace tailWord_832982 prefixEnd_832982 380195682260946833594837 := by
  unfold tailWord_832982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898834341765996927790825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20254232978837300563102133 1898834341765996927790825)
  ·
    refine ⟨1424125756324497695843119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1898834341765996927790825 1424125756324497695843119)
    ·
      refine ⟨2136188634486746543764679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424125756324497695843119 2136188634486746543764679)
      ·
        refine ⟨3204282951730119815647019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136188634486746543764679 3204282951730119815647019)
        ·
          refine ⟨4806424427595179723470529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204282951730119815647019 4806424427595179723470529)
          ·
            refine ⟨3604818320696384792602897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4806424427595179723470529 3604818320696384792602897)
            ·
              refine ⟨2703613740522288594452173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604818320696384792602897 2703613740522288594452173)
              ·
                refine ⟨1013855152695858222919565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2703613740522288594452173 1013855152695858222919565)
                ·
                  refine ⟨380195682260946833594837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013855152695858222919565 380195682260946833594837)
                  ·
                    rfl

theorem cell20_832982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_832982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832982 prefixEnd_832982 := by exact prefixLift 832982
  have htrace : WordTrace (prefixWord ++ tailWord_832982) baseStart_832982 baseEnd_832982 := by
    simpa [prefixWord, tailWord_832982, baseEnd_832982] using wordTrace_append hprefix tailTrace_832982
  have hstable : (prefixWord ++ tailWord_832982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832982).length < 2 ^ (prefixWord ++ tailWord_832982).sum := by decide
  have hdescent : baseEnd_832982 < baseStart_832982 := by decide
  rcases family_descends (prefixWord ++ tailWord_832982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832993 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_832993 : Nat := 118140960795 + 832993 * 2 ^ 59
def prefixEnd_832993 : Nat := 4983230072969 + 3 ^ 40 * 832993 * 2
def baseEnd_832993 : Nat := 380200702960679684228125

theorem tailTrace_832993 : CollatzResearch.WordTrace tailWord_832993 prefixEnd_832993 380200702960679684228125 := by
  unfold tailWord_832993
  simp only [CollatzResearch.WordTrace]
  refine ⟨30381750671216099723303633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20254500447477399815535755 30381750671216099723303633)
  ·
    refine ⟨22786313003412074792477725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30381750671216099723303633 22786313003412074792477725)
    ·
      refine ⟨8544867376279528047179147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22786313003412074792477725 8544867376279528047179147)
      ·
        refine ⟨12817301064419292070768721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8544867376279528047179147 12817301064419292070768721)
        ·
          refine ⟨9612975798314469053076541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12817301064419292070768721 9612975798314469053076541)
          ·
            refine ⟨3604865924367925894903703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9612975798314469053076541 3604865924367925894903703)
            ·
              refine ⟨5407298886551888842355555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604865924367925894903703 5407298886551888842355555)
              ·
                refine ⟨8110948329827833263533333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407298886551888842355555 8110948329827833263533333)
                ·
                  refine ⟨380200702960679684228125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8110948329827833263533333 380200702960679684228125)
                  ·
                    rfl

theorem cell20_832993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_832993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832993 prefixEnd_832993 := by exact prefixLift 832993
  have htrace : WordTrace (prefixWord ++ tailWord_832993) baseStart_832993 baseEnd_832993 := by
    simpa [prefixWord, tailWord_832993, baseEnd_832993] using wordTrace_append hprefix tailTrace_832993
  have hstable : (prefixWord ++ tailWord_832993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832993).length < 2 ^ (prefixWord ++ tailWord_832993).sum := by decide
  have hdescent : baseEnd_832993 < baseStart_832993 := by decide
  rcases family_descends (prefixWord ++ tailWord_832993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833041 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 3]
def baseStart_833041 : Nat := 118140960795 + 833041 * 2 ^ 59
def prefixEnd_833041 : Nat := 4983230072969 + 3 ^ 40 * 833041 * 2
def baseEnd_833041 : Nat := 380222611468604850627929

theorem tailTrace_833041 : CollatzResearch.WordTrace tailWord_833041 prefixEnd_833041 380222611468604850627929 := by
  unfold tailWord_833041
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383501375042203921050977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20255667583361469280700651 30383501375042203921050977)
  ·
    refine ⟨22787626031281652940788233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30383501375042203921050977 22787626031281652940788233)
    ·
      refine ⟨17090719523461239705591175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22787626031281652940788233 17090719523461239705591175)
      ·
        refine ⟨25636079285191859558386763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17090719523461239705591175 25636079285191859558386763)
        ·
          refine ⟨38454118927787789337580145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25636079285191859558386763 38454118927787789337580145)
          ·
            refine ⟨28840589195840842003185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38454118927787789337580145 28840589195840842003185109)
            ·
              refine ⟨675951309277519734449651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28840589195840842003185109 675951309277519734449651)
              ·
                refine ⟨1013926963916279601674477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675951309277519734449651 1013926963916279601674477)
                ·
                  refine ⟨380222611468604850627929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013926963916279601674477 380222611468604850627929)
                  ·
                    rfl

theorem cell20_833041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_833041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833041 prefixEnd_833041 := by exact prefixLift 833041
  have htrace : WordTrace (prefixWord ++ tailWord_833041) baseStart_833041 baseEnd_833041 := by
    simpa [prefixWord, tailWord_833041, baseEnd_833041] using wordTrace_append hprefix tailTrace_833041
  have hstable : (prefixWord ++ tailWord_833041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833041).length < 2 ^ (prefixWord ++ tailWord_833041).sum := by decide
  have hdescent : baseEnd_833041 < baseStart_833041 := by decide
  rcases family_descends (prefixWord ++ tailWord_833041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833055 : List Nat := [1, 1, 2, 4, 1, 1, 6, 4]
def baseStart_833055 : Nat := 118140960795 + 833055 * 2 ^ 59
def prefixEnd_833055 : Nat := 4983230072969 + 3 ^ 40 * 833055 * 2
def baseEnd_833055 : Nat := 126743000483361008053735

theorem tailTrace_833055 : CollatzResearch.WordTrace tailWord_833055 prefixEnd_833055 126743000483361008053735 := by
  unfold tailWord_833055
  simp only [CollatzResearch.WordTrace]
  refine ⟨30384011996991484312060619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20256007997994322874707079 30384011996991484312060619)
  ·
    refine ⟨45576017995487226468090929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30384011996991484312060619 45576017995487226468090929)
    ·
      refine ⟨34182013496615419851068197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45576017995487226468090929 34182013496615419851068197)
      ·
        refine ⟨6409127530615391222075287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34182013496615419851068197 6409127530615391222075287)
        ·
          refine ⟨9613691295923086833112931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409127530615391222075287 9613691295923086833112931)
          ·
            refine ⟨14420536943884630249669397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613691295923086833112931 14420536943884630249669397)
            ·
              refine ⟨675962669244592042953253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14420536943884630249669397 675962669244592042953253)
              ·
                refine ⟨126743000483361008053735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675962669244592042953253 126743000483361008053735)
                ·
                  rfl

theorem cell20_833055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_833055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833055 prefixEnd_833055 := by exact prefixLift 833055
  have htrace : WordTrace (prefixWord ++ tailWord_833055) baseStart_833055 baseEnd_833055 := by
    simpa [prefixWord, tailWord_833055, baseEnd_833055] using wordTrace_append hprefix tailTrace_833055
  have hstable : (prefixWord ++ tailWord_833055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833055).length < 2 ^ (prefixWord ++ tailWord_833055).sum := by decide
  have hdescent : baseEnd_833055 < baseStart_833055 := by decide
  rcases family_descends (prefixWord ++ tailWord_833055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833134 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_833134 : Nat := 118140960795 + 833134 * 2 ^ 59
def prefixEnd_833134 : Nat := 4983230072969 + 3 ^ 40 * 833134 * 2
def baseEnd_833134 : Nat := 380265059202709860527549

theorem tailTrace_833134 : CollatzResearch.WordTrace tailWord_833134 prefixEnd_833134 380265059202709860527549 := by
  unfold tailWord_833134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798361670463160100523307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20257928909136853869457637 3798361670463160100523307)
  ·
    refine ⟨5697542505694740150784961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3798361670463160100523307 5697542505694740150784961)
    ·
      refine ⟨4273156879271055113088721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5697542505694740150784961 4273156879271055113088721)
      ·
        refine ⟨3204867659453291334816541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273156879271055113088721 3204867659453291334816541)
        ·
          refine ⟨1201825372294984250556203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3204867659453291334816541 1201825372294984250556203)
          ·
            refine ⟨1802738058442476375834305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201825372294984250556203 1802738058442476375834305)
            ·
              refine ⟨1352053543831857281875729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1802738058442476375834305 1352053543831857281875729)
              ·
                refine ⟨1014040157873892961406797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352053543831857281875729 1014040157873892961406797)
                ·
                  refine ⟨380265059202709860527549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014040157873892961406797 380265059202709860527549)
                  ·
                    rfl

theorem cell20_833134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_833134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833134 prefixEnd_833134 := by exact prefixLift 833134
  have htrace : WordTrace (prefixWord ++ tailWord_833134) baseStart_833134 baseEnd_833134 := by
    simpa [prefixWord, tailWord_833134, baseEnd_833134] using wordTrace_append hprefix tailTrace_833134
  have hstable : (prefixWord ++ tailWord_833134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833134).length < 2 ^ (prefixWord ++ tailWord_833134).sum := by decide
  have hdescent : baseEnd_833134 < baseStart_833134 := by decide
  rcases family_descends (prefixWord ++ tailWord_833134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833145 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_833145 : Nat := 118140960795 + 833145 * 2 ^ 59
def prefixEnd_833145 : Nat := 4983230072969 + 3 ^ 40 * 833145 * 2
def baseEnd_833145 : Nat := 380270079902442711160837

theorem tailTrace_833145 : CollatzResearch.WordTrace tailWord_833145 prefixEnd_833145 380270079902442711160837 := by
  unfold tailWord_833145
  simp only [CollatzResearch.WordTrace]
  refine ⟨30387294566665429682836889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20258196377776953121891259 30387294566665429682836889)
  ·
    refine ⟨22790470924999072262127667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30387294566665429682836889 22790470924999072262127667)
    ·
      refine ⟨34185706387498608393191501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22790470924999072262127667 34185706387498608393191501)
      ·
        refine ⟨12819639895311978147446813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34185706387498608393191501 12819639895311978147446813)
        ·
          refine ⟨4807364960741991805292555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12819639895311978147446813 4807364960741991805292555)
          ·
            refine ⟨7211047441112987707938833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807364960741991805292555 7211047441112987707938833)
            ·
              refine ⟨5408285580834740780954125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211047441112987707938833 5408285580834740780954125)
              ·
                refine ⟨2028107092813027792857797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5408285580834740780954125 2028107092813027792857797)
                ·
                  refine ⟨380270079902442711160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028107092813027792857797 380270079902442711160837)
                  ·
                    rfl

theorem cell20_833145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_833145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833145 prefixEnd_833145 := by exact prefixLift 833145
  have htrace : WordTrace (prefixWord ++ tailWord_833145) baseStart_833145 baseEnd_833145 := by
    simpa [prefixWord, tailWord_833145, baseEnd_833145] using wordTrace_append hprefix tailTrace_833145
  have hstable : (prefixWord ++ tailWord_833145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833145).length < 2 ^ (prefixWord ++ tailWord_833145).sum := by decide
  have hdescent : baseEnd_833145 < baseStart_833145 := by decide
  rcases family_descends (prefixWord ++ tailWord_833145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833162 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_833162 : Nat := 118140960795 + 833162 * 2 ^ 59
def prefixEnd_833162 : Nat := 4983230072969 + 3 ^ 40 * 833162 * 2
def baseEnd_833162 : Nat := 380277839165666207594101

theorem tailTrace_833162 : CollatzResearch.WordTrace tailWord_833162 prefixEnd_833162 380277839165666207594101 := by
  unfold tailWord_833162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596978651900960396551435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20258609738402561057470493 7596978651900960396551435)
  ·
    refine ⟨11395467977851440594827153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7596978651900960396551435 11395467977851440594827153)
    ·
      refine ⟨8546600983388580446120365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11395467977851440594827153 8546600983388580446120365)
      ·
        refine ⟨3204975368770717667295137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8546600983388580446120365 3204975368770717667295137)
        ·
          refine ⟨2403731526578038250471353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3204975368770717667295137 2403731526578038250471353)
          ·
            refine ⟨1802798644933528687853515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2403731526578038250471353 1802798644933528687853515)
            ·
              refine ⟨2704197967400293031780273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802798644933528687853515 2704197967400293031780273)
              ·
                refine ⟨2028148475550219773835205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704197967400293031780273 2028148475550219773835205)
                ·
                  refine ⟨380277839165666207594101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028148475550219773835205 380277839165666207594101)
                  ·
                    rfl

theorem cell20_833162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_833162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833162 prefixEnd_833162 := by exact prefixLift 833162
  have htrace : WordTrace (prefixWord ++ tailWord_833162) baseStart_833162 baseEnd_833162 := by
    simpa [prefixWord, tailWord_833162, baseEnd_833162] using wordTrace_append hprefix tailTrace_833162
  have hstable : (prefixWord ++ tailWord_833162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833162).length < 2 ^ (prefixWord ++ tailWord_833162).sum := by decide
  have hdescent : baseEnd_833162 < baseStart_833162 := by decide
  rcases family_descends (prefixWord ++ tailWord_833162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833186 : List Nat := [3, 3, 1, 4, 1, 1, 7]
def baseStart_833186 : Nat := 118140960795 + 833186 * 2 ^ 59
def prefixEnd_833186 : Nat := 4983230072969 + 3 ^ 40 * 833186 * 2
def baseEnd_833186 : Nat := 42254310379958754532667

theorem tailTrace_833186 : CollatzResearch.WordTrace tailWord_833186 prefixEnd_833186 42254310379958754532667 := by
  unfold tailWord_833186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597197489879223421269853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20259193306344595790052941 7597197489879223421269853)
  ·
    refine ⟨2848949058704708782976195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7597197489879223421269853 2848949058704708782976195)
    ·
      refine ⟨4273423588057063174464293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848949058704708782976195 4273423588057063174464293)
      ·
        refine ⟨801266922760699345212055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4273423588057063174464293 801266922760699345212055)
        ·
          refine ⟨1201900384141049017818083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801266922760699345212055 1201900384141049017818083)
          ·
            refine ⟨1802850576211573526727125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201900384141049017818083 1802850576211573526727125)
            ·
              refine ⟨42254310379958754532667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1802850576211573526727125 42254310379958754532667)
              ·
                rfl

theorem cell20_833186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 7].length) (baseStart_833186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833186 prefixEnd_833186 := by exact prefixLift 833186
  have htrace : WordTrace (prefixWord ++ tailWord_833186) baseStart_833186 baseEnd_833186 := by
    simpa [prefixWord, tailWord_833186, baseEnd_833186] using wordTrace_append hprefix tailTrace_833186
  have hstable : (prefixWord ++ tailWord_833186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833186).length < 2 ^ (prefixWord ++ tailWord_833186).sum := by decide
  have hdescent : baseEnd_833186 < baseStart_833186 := by decide
  rcases family_descends (prefixWord ++ tailWord_833186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833200 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 2]
def baseStart_833200 : Nat := 118140960795 + 833200 * 2 ^ 59
def prefixEnd_833200 : Nat := 4983230072969 + 3 ^ 40 * 833200 * 2
def baseEnd_833200 : Nat := 380295183401106964327279

theorem tailTrace_833200 : CollatzResearch.WordTrace tailWord_833200 prefixEnd_833200 380295183401106964327279 := by
  unfold tailWord_833200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15194650290733087038044527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20259533720977449384059369 15194650290733087038044527)
  ·
    refine ⟨22791975436099630557066791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15194650290733087038044527 22791975436099630557066791)
    ·
      refine ⟨34187963154149445835600187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22791975436099630557066791 34187963154149445835600187)
      ·
        refine ⟨51281944731224168753400281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34187963154149445835600187 51281944731224168753400281)
        ·
          refine ⟨38461458548418126565050211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51281944731224168753400281 38461458548418126565050211)
          ·
            refine ⟨57692187822627189847575317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38461458548418126565050211 57692187822627189847575317)
            ·
              refine ⟨2704321304185649524105093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57692187822627189847575317 2704321304185649524105093)
              ·
                refine ⟨507060244534809285769705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2704321304185649524105093 507060244534809285769705)
                ·
                  refine ⟨380295183401106964327279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507060244534809285769705 380295183401106964327279)
                  ·
                    rfl

theorem cell20_833200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_833200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833200 prefixEnd_833200 := by exact prefixLift 833200
  have htrace : WordTrace (prefixWord ++ tailWord_833200) baseStart_833200 baseEnd_833200 := by
    simpa [prefixWord, tailWord_833200, baseEnd_833200] using wordTrace_append hprefix tailTrace_833200
  have hstable : (prefixWord ++ tailWord_833200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833200).length < 2 ^ (prefixWord ++ tailWord_833200).sum := by decide
  have hdescent : baseEnd_833200 < baseStart_833200 := by decide
  rcases family_descends (prefixWord ++ tailWord_833200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833234 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_833234 : Nat := 118140960795 + 833234 * 2 ^ 59
def prefixEnd_833234 : Nat := 4983230072969 + 3 ^ 40 * 833234 * 2
def baseEnd_833234 : Nat := 380310701927553957193807

theorem tailTrace_833234 : CollatzResearch.WordTrace tailWord_833234 prefixEnd_833234 380310701927553957193807 := by
  unfold tailWord_833234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597635165835749470706689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20260360442228665255217837 7597635165835749470706689)
  ·
    refine ⟨5698226374376812103030017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7597635165835749470706689 5698226374376812103030017)
    ·
      refine ⟨4273669780782609077272513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5698226374376812103030017 4273669780782609077272513)
      ·
        refine ⟨3205252335586956807954385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273669780782609077272513 3205252335586956807954385)
        ·
          refine ⟨2403939251690217605965789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3205252335586956807954385 2403939251690217605965789)
          ·
            refine ⟨901477219383831602237171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2403939251690217605965789 901477219383831602237171)
            ·
              refine ⟨1352215829075747403355757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901477219383831602237171 1352215829075747403355757)
              ·
                refine ⟨507080935903405276258409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352215829075747403355757 507080935903405276258409)
                ·
                  refine ⟨380310701927553957193807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507080935903405276258409 380310701927553957193807)
                  ·
                    rfl

theorem cell20_833234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_833234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833234 prefixEnd_833234 := by exact prefixLift 833234
  have htrace : WordTrace (prefixWord ++ tailWord_833234) baseStart_833234 baseEnd_833234 := by
    simpa [prefixWord, tailWord_833234, baseEnd_833234] using wordTrace_append hprefix tailTrace_833234
  have hstable : (prefixWord ++ tailWord_833234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833234).length < 2 ^ (prefixWord ++ tailWord_833234).sum := by decide
  have hdescent : baseEnd_833234 < baseStart_833234 := by decide
  rcases family_descends (prefixWord ++ tailWord_833234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833252 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_833252 : Nat := 118140960795 + 833252 * 2 ^ 59
def prefixEnd_833252 : Nat := 4983230072969 + 3 ^ 40 * 833252 * 2
def baseEnd_833252 : Nat := 380318917618025894593733

theorem tailTrace_833252 : CollatzResearch.WordTrace tailWord_833252 prefixEnd_833252 380318917618025894593733 := by
  unfold tailWord_833252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15195598588638893478491005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20260798118185191304654673 15195598588638893478491005)
  ·
    refine ⟨5698349470739585054434127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15195598588638893478491005 5698349470739585054434127)
    ·
      refine ⟨8547524206109377581651191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698349470739585054434127 8547524206109377581651191)
      ·
        refine ⟨12821286309164066372476787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547524206109377581651191 12821286309164066372476787)
        ·
          refine ⟨19231929463746099558715181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821286309164066372476787 19231929463746099558715181)
          ·
            refine ⟨7211973548904787334518193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19231929463746099558715181 7211973548904787334518193)
            ·
              refine ⟨5408980161678590500888645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211973548904787334518193 5408980161678590500888645)
              ·
                refine ⟨1014183780314735718916621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5408980161678590500888645 1014183780314735718916621)
                ·
                  refine ⟨380318917618025894593733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014183780314735718916621 380318917618025894593733)
                  ·
                    rfl

theorem cell20_833252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_833252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833252 prefixEnd_833252 := by exact prefixLift 833252
  have htrace : WordTrace (prefixWord ++ tailWord_833252) baseStart_833252 baseEnd_833252 := by
    simpa [prefixWord, tailWord_833252, baseEnd_833252] using wordTrace_append hprefix tailTrace_833252
  have hstable : (prefixWord ++ tailWord_833252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833252).length < 2 ^ (prefixWord ++ tailWord_833252).sum := by decide
  have hdescent : baseEnd_833252 < baseStart_833252 := by decide
  rcases family_descends (prefixWord ++ tailWord_833252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833259 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_833259 : Nat := 118140960795 + 833259 * 2 ^ 59
def prefixEnd_833259 : Nat := 4983230072969 + 3 ^ 40 * 833259 * 2
def baseEnd_833259 : Nat := 380322112608764981360371

theorem tailTrace_833259 : CollatzResearch.WordTrace tailWord_833259 prefixEnd_833259 380322112608764981360371 := by
  unfold tailWord_833259
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391452488252427152486831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20260968325501618101657887 30391452488252427152486831)
  ·
    refine ⟨45587178732378640728730247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30391452488252427152486831 45587178732378640728730247)
    ·
      refine ⟨68380768098567961093095371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45587178732378640728730247 68380768098567961093095371)
      ·
        refine ⟨102571152147851941639643057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68380768098567961093095371 102571152147851941639643057)
        ·
          refine ⟨76928364110888956229732293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102571152147851941639643057 76928364110888956229732293)
          ·
            refine ⟨14424068270791679293074805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76928364110888956229732293 14424068270791679293074805)
            ·
              refine ⟨1352256400386719933725763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14424068270791679293074805 1352256400386719933725763)
              ·
                refine ⟨2028384600580079900588645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352256400386719933725763 2028384600580079900588645)
                ·
                  refine ⟨380322112608764981360371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028384600580079900588645 380322112608764981360371)
                  ·
                    rfl

theorem cell20_833259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_833259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833259 prefixEnd_833259 := by exact prefixLift 833259
  have htrace : WordTrace (prefixWord ++ tailWord_833259) baseStart_833259 baseEnd_833259 := by
    simpa [prefixWord, tailWord_833259, baseEnd_833259] using wordTrace_append hprefix tailTrace_833259
  have hstable : (prefixWord ++ tailWord_833259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833259).length < 2 ^ (prefixWord ++ tailWord_833259).sum := by decide
  have hdescent : baseEnd_833259 < baseStart_833259 := by decide
  rcases family_descends (prefixWord ++ tailWord_833259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833300 : List Nat := [2, 4, 4, 1, 9]
def baseStart_833300 : Nat := 118140960795 + 833300 * 2 ^ 59
def prefixEnd_833300 : Nat := 4983230072969 + 3 ^ 40 * 833300 * 2
def baseEnd_833300 : Nat := 4695565754641371123377

theorem tailTrace_833300 : CollatzResearch.WordTrace tailWord_833300 prefixEnd_833300 4695565754641371123377 := by
  unfold tailWord_833300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196473940551945577364677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20261965254069260769819569 15196473940551945577364677)
  ·
    refine ⟨2849338863853489795755877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15196473940551945577364677 2849338863853489795755877)
    ·
      refine ⟨534251036972529336704227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2849338863853489795755877 534251036972529336704227)
      ·
        refine ⟨801376555458794005056341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534251036972529336704227 801376555458794005056341)
        ·
          refine ⟨4695565754641371123377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 801376555458794005056341 4695565754641371123377)
          ·
            rfl

theorem cell20_833300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 9].length) (baseStart_833300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833300 prefixEnd_833300 := by exact prefixLift 833300
  have htrace : WordTrace (prefixWord ++ tailWord_833300) baseStart_833300 baseEnd_833300 := by
    simpa [prefixWord, tailWord_833300, baseEnd_833300] using wordTrace_append hprefix tailTrace_833300
  have hstable : (prefixWord ++ tailWord_833300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833300).length < 2 ^ (prefixWord ++ tailWord_833300).sum := by decide
  have hdescent : baseEnd_833300 < baseStart_833300 := by decide
  rcases family_descends (prefixWord ++ tailWord_833300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833349 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_833349 : Nat := 118140960795 + 833349 * 2 ^ 59
def prefixEnd_833349 : Nat := 4983230072969 + 3 ^ 40 * 833349 * 2
def baseEnd_833349 : Nat := 380363191061124668360003

theorem tailTrace_833349 : CollatzResearch.WordTrace tailWord_833349 prefixEnd_833349 380363191061124668360003 := by
  unfold tailWord_833349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30394735057926372523263101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20263156705284248348842067 30394735057926372523263101)
  ·
    refine ⟨11398025646722389696223663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30394735057926372523263101 11398025646722389696223663)
    ·
      refine ⟨17097038470083584544335495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11398025646722389696223663 17097038470083584544335495)
      ·
        refine ⟨25645557705125376816503243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17097038470083584544335495 25645557705125376816503243)
        ·
          refine ⟨38468336557688065224754865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25645557705125376816503243 38468336557688065224754865)
          ·
            refine ⟨28851252418266048918566149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38468336557688065224754865 28851252418266048918566149)
            ·
              refine ⟨5409609828424884172231153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28851252418266048918566149 5409609828424884172231153)
              ·
                refine ⟨4057207371318663129173365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409609828424884172231153 4057207371318663129173365)
                ·
                  refine ⟨380363191061124668360003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4057207371318663129173365 380363191061124668360003)
                  ·
                    rfl

theorem cell20_833349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_833349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833349 prefixEnd_833349 := by exact prefixLift 833349
  have htrace : WordTrace (prefixWord ++ tailWord_833349) baseStart_833349 baseEnd_833349 := by
    simpa [prefixWord, tailWord_833349, baseEnd_833349] using wordTrace_append hprefix tailTrace_833349
  have hstable : (prefixWord ++ tailWord_833349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833349).length < 2 ^ (prefixWord ++ tailWord_833349).sum := by decide
  have hdescent : baseEnd_833349 < baseStart_833349 := by decide
  rcases family_descends (prefixWord ++ tailWord_833349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833352 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 2]
def baseStart_833352 : Nat := 118140960795 + 833352 * 2 ^ 59
def prefixEnd_833352 : Nat := 4983230072969 + 3 ^ 40 * 833352 * 2
def baseEnd_833352 : Nat := 380364560342869991259991

theorem tailTrace_833352 : CollatzResearch.WordTrace tailWord_833352 prefixEnd_833352 380364560342869991259991 := by
  unfold tailWord_833352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197422238457752017811155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20263229651277002690414873 15197422238457752017811155)
  ·
    refine ⟨22796133357686628026716733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15197422238457752017811155 22796133357686628026716733)
    ·
      refine ⟨8548550009132485510018775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22796133357686628026716733 8548550009132485510018775)
      ·
        refine ⟨12822825013698728265028163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8548550009132485510018775 12822825013698728265028163)
        ·
          refine ⟨19234237520548092397542245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822825013698728265028163 19234237520548092397542245)
          ·
            refine ⟨3606419535102767324539171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19234237520548092397542245 3606419535102767324539171)
            ·
              refine ⟨5409629302654150986808757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606419535102767324539171 5409629302654150986808757)
              ·
                refine ⟨507152747123826655013321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5409629302654150986808757 507152747123826655013321)
                ·
                  refine ⟨380364560342869991259991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507152747123826655013321 380364560342869991259991)
                  ·
                    rfl

theorem cell20_833352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_833352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833352 prefixEnd_833352 := by exact prefixLift 833352
  have htrace : WordTrace (prefixWord ++ tailWord_833352) baseStart_833352 baseEnd_833352 := by
    simpa [prefixWord, tailWord_833352, baseEnd_833352] using wordTrace_append hprefix tailTrace_833352
  have hstable : (prefixWord ++ tailWord_833352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833352).length < 2 ^ (prefixWord ++ tailWord_833352).sum := by decide
  have hdescent : baseEnd_833352 < baseStart_833352 := by decide
  rcases family_descends (prefixWord ++ tailWord_833352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833383 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 3]
def baseStart_833383 : Nat := 118140960795 + 833383 * 2 ^ 59
def prefixEnd_833383 : Nat := 4983230072969 + 3 ^ 40 * 833383 * 2
def baseEnd_833383 : Nat := 380378709587571661226531

theorem tailTrace_833383 : CollatzResearch.WordTrace tailWord_833383 prefixEnd_833383 380378709587571661226531 := by
  unfold tailWord_833383
  simp only [CollatzResearch.WordTrace]
  refine ⟨30395975139803196330000803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20263983426535464220000535 30395975139803196330000803)
  ·
    refine ⟨45593962709704794495001205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30395975139803196330000803 45593962709704794495001205)
    ·
      refine ⟨4274434004034824483906363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45593962709704794495001205 4274434004034824483906363)
      ·
        refine ⟨6411651006052236725859545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274434004034824483906363 6411651006052236725859545)
        ·
          refine ⟨4808738254539177544394659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6411651006052236725859545 4808738254539177544394659)
          ·
            refine ⟨7213107381808766316591989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808738254539177544394659 7213107381808766316591989)
            ·
              refine ⟨676228817044571842180499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7213107381808766316591989 676228817044571842180499)
              ·
                refine ⟨1014343225566857763270749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676228817044571842180499 1014343225566857763270749)
                ·
                  refine ⟨380378709587571661226531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014343225566857763270749 380378709587571661226531)
                  ·
                    rfl

theorem cell20_833383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_833383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833383 prefixEnd_833383 := by exact prefixLift 833383
  have htrace : WordTrace (prefixWord ++ tailWord_833383) baseStart_833383 baseEnd_833383 := by
    simpa [prefixWord, tailWord_833383, baseEnd_833383] using wordTrace_append hprefix tailTrace_833383
  have hstable : (prefixWord ++ tailWord_833383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833383).length < 2 ^ (prefixWord ++ tailWord_833383).sum := by decide
  have hdescent : baseEnd_833383 < baseStart_833383 := by decide
  rcases family_descends (prefixWord ++ tailWord_833383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833390 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_833390 : Nat := 118140960795 + 833390 * 2 ^ 59
def prefixEnd_833390 : Nat := 4983230072969 + 3 ^ 40 * 833390 * 2
def baseEnd_833390 : Nat := 380381904578310747993169

theorem tailTrace_833390 : CollatzResearch.WordTrace tailWord_833390 prefixEnd_833390 380381904578310747993169 := by
  unfold tailWord_833390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799528806347229565688203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20264153633851891017003749 3799528806347229565688203)
  ·
    refine ⟨5699293209520844348532305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3799528806347229565688203 5699293209520844348532305)
    ·
      refine ⟨4274469907140633261399229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5699293209520844348532305 4274469907140633261399229)
      ·
        refine ⟨1602926215177737473024711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4274469907140633261399229 1602926215177737473024711)
        ·
          refine ⟨2404389322766606209537067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602926215177737473024711 2404389322766606209537067)
          ·
            refine ⟨3606583984149909314305601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404389322766606209537067 3606583984149909314305601)
            ·
              refine ⟨2704937988112431985729201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606583984149909314305601 2704937988112431985729201)
              ·
                refine ⟨2028703491084323989296901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704937988112431985729201 2028703491084323989296901)
                ·
                  refine ⟨380381904578310747993169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028703491084323989296901 380381904578310747993169)
                  ·
                    rfl

theorem cell20_833390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_833390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833390 prefixEnd_833390 := by exact prefixLift 833390
  have htrace : WordTrace (prefixWord ++ tailWord_833390) baseStart_833390 baseEnd_833390 := by
    simpa [prefixWord, tailWord_833390, baseEnd_833390] using wordTrace_append hprefix tailTrace_833390
  have hstable : (prefixWord ++ tailWord_833390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833390).length < 2 ^ (prefixWord ++ tailWord_833390).sum := by decide
  have hdescent : baseEnd_833390 < baseStart_833390 := by decide
  rcases family_descends (prefixWord ++ tailWord_833390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833425 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_833425 : Nat := 118140960795 + 833425 * 2 ^ 59
def prefixEnd_833425 : Nat := 4983230072969 + 3 ^ 40 * 833425 * 2
def baseEnd_833425 : Nat := 380397879532006181826359

theorem tailTrace_833425 : CollatzResearch.WordTrace tailWord_833425 prefixEnd_833425 380397879532006181826359 := by
  unfold tailWord_833425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30397507005651037503029729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20265004670434025002019819 30397507005651037503029729)
  ·
    refine ⟨22798130254238278127272297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30397507005651037503029729 22798130254238278127272297)
    ·
      refine ⟨17098597690678708595454223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22798130254238278127272297 17098597690678708595454223)
      ·
        refine ⟨25647896536018062893181335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17098597690678708595454223 25647896536018062893181335)
        ·
          refine ⟨38471844804027094339772003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25647896536018062893181335 38471844804027094339772003)
          ·
            refine ⟨57707767206040641509658005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38471844804027094339772003 57707767206040641509658005)
            ·
              refine ⟨2705051587783155070765219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57707767206040641509658005 2705051587783155070765219)
              ·
                refine ⟨4057577381674732606147829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705051587783155070765219 4057577381674732606147829)
                ·
                  refine ⟨380397879532006181826359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4057577381674732606147829 380397879532006181826359)
                  ·
                    rfl

theorem cell20_833425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_833425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833425 prefixEnd_833425 := by exact prefixLift 833425
  have htrace : WordTrace (prefixWord ++ tailWord_833425) baseStart_833425 baseEnd_833425 := by
    simpa [prefixWord, tailWord_833425, baseEnd_833425] using wordTrace_append hprefix tailTrace_833425
  have hstable : (prefixWord ++ tailWord_833425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833425).length < 2 ^ (prefixWord ++ tailWord_833425).sum := by decide
  have hdescent : baseEnd_833425 < baseStart_833425 := by decide
  rcases family_descends (prefixWord ++ tailWord_833425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833428 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_833428 : Nat := 118140960795 + 833428 * 2 ^ 59
def prefixEnd_833428 : Nat := 4983230072969 + 3 ^ 40 * 833428 * 2
def baseEnd_833428 : Nat := 380399248813751504726347

theorem tailTrace_833428 : CollatzResearch.WordTrace tailWord_833428 prefixEnd_833428 380399248813751504726347 := by
  unfold tailWord_833428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15198808212320084507694469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20265077616426779343592625 15198808212320084507694469)
  ·
    refine ⟨2849776539810015845192713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15198808212320084507694469 2849776539810015845192713)
    ·
      refine ⟨2137332404857511883894535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849776539810015845192713 2137332404857511883894535)
      ·
        refine ⟨3205998607286267825841803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137332404857511883894535 3205998607286267825841803)
        ·
          refine ⟨4808997910929401738762705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205998607286267825841803 4808997910929401738762705)
          ·
            refine ⟨3606748433197051304072029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808997910929401738762705 3606748433197051304072029)
            ·
              refine ⟨1352530662448894239027011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3606748433197051304072029 1352530662448894239027011)
              ·
                refine ⟨2028795993673341358540517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352530662448894239027011 2028795993673341358540517)
                ·
                  refine ⟨380399248813751504726347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028795993673341358540517 380399248813751504726347)
                  ·
                    rfl

theorem cell20_833428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_833428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833428 prefixEnd_833428 := by exact prefixLift 833428
  have htrace : WordTrace (prefixWord ++ tailWord_833428) baseStart_833428 baseEnd_833428 := by
    simpa [prefixWord, tailWord_833428, baseEnd_833428] using wordTrace_append hprefix tailTrace_833428
  have hstable : (prefixWord ++ tailWord_833428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833428).length < 2 ^ (prefixWord ++ tailWord_833428).sum := by decide
  have hdescent : baseEnd_833428 < baseStart_833428 := by decide
  rcases family_descends (prefixWord ++ tailWord_833428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833480 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_833480 : Nat := 118140960795 + 833480 * 2 ^ 59
def prefixEnd_833480 : Nat := 4983230072969 + 3 ^ 40 * 833480 * 2
def baseEnd_833480 : Nat := 380422983030670434992801

theorem tailTrace_833480 : CollatzResearch.WordTrace tailWord_833480 prefixEnd_833480 380422983030670434992801 := by
  unfold tailWord_833480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15199756510225890948140947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20266342013634521264187929 15199756510225890948140947)
  ·
    refine ⟨22799634765338836422211421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15199756510225890948140947 22799634765338836422211421)
    ·
      refine ⟨8549863037002063658329283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22799634765338836422211421 8549863037002063658329283)
      ·
        refine ⟨12824794555503095487493925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549863037002063658329283 12824794555503095487493925)
        ·
          refine ⟨2404648979156830403905111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12824794555503095487493925 2404648979156830403905111)
          ·
            refine ⟨3606973468735245605857667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404648979156830403905111 3606973468735245605857667)
            ·
              refine ⟨5410460203102868408786501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606973468735245605857667 5410460203102868408786501)
              ·
                refine ⟨1014461288081787826647469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5410460203102868408786501 1014461288081787826647469)
                ·
                  refine ⟨380422983030670434992801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014461288081787826647469 380422983030670434992801)
                  ·
                    rfl

theorem cell20_833480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_833480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833480 prefixEnd_833480 := by exact prefixLift 833480
  have htrace : WordTrace (prefixWord ++ tailWord_833480) baseStart_833480 baseEnd_833480 := by
    simpa [prefixWord, tailWord_833480, baseEnd_833480] using wordTrace_append hprefix tailTrace_833480
  have hstable : (prefixWord ++ tailWord_833480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833480).length < 2 ^ (prefixWord ++ tailWord_833480).sum := by decide
  have hdescent : baseEnd_833480 < baseStart_833480 := by decide
  rcases family_descends (prefixWord ++ tailWord_833480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833490 : List Nat := [3, 2, 2, 3, 2, 2, 1, 5]
def baseStart_833490 : Nat := 118140960795 + 833490 * 2 ^ 59
def prefixEnd_833490 : Nat := 4983230072969 + 3 ^ 40 * 833490 * 2
def baseEnd_833490 : Nat := 126809182434384948219809

theorem tailTrace_833490 : CollatzResearch.WordTrace tailWord_833490 prefixEnd_833490 126809182434384948219809 := by
  unfold tailWord_833490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599969437603888401036481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20266585166943702402763949 7599969437603888401036481)
  ·
    refine ⟨5699977078202916300777361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7599969437603888401036481 5699977078202916300777361)
    ·
      refine ⟨4274982808652187225583021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5699977078202916300777361 4274982808652187225583021)
      ·
        refine ⟨1603118553244570209593633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4274982808652187225583021 1603118553244570209593633)
        ·
          refine ⟨1202338914933427657195225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603118553244570209593633 1202338914933427657195225)
          ·
            refine ⟨901754186200070742896419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202338914933427657195225 901754186200070742896419)
            ·
              refine ⟨1352631279300106114344629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901754186200070742896419 1352631279300106114344629)
              ·
                refine ⟨126809182434384948219809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1352631279300106114344629 126809182434384948219809)
                ·
                  rfl

theorem cell20_833490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_833490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833490 prefixEnd_833490 := by exact prefixLift 833490
  have htrace : WordTrace (prefixWord ++ tailWord_833490) baseStart_833490 baseEnd_833490 := by
    simpa [prefixWord, tailWord_833490, baseEnd_833490] using wordTrace_append hprefix tailTrace_833490
  have hstable : (prefixWord ++ tailWord_833490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833490).length < 2 ^ (prefixWord ++ tailWord_833490).sum := by decide
  have hdescent : baseEnd_833490 < baseStart_833490 := by decide
  rcases family_descends (prefixWord ++ tailWord_833490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833500 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 4]
def baseStart_833500 : Nat := 118140960795 + 833500 * 2 ^ 59
def prefixEnd_833500 : Nat := 4983230072969 + 3 ^ 40 * 833500 * 2
def baseEnd_833500 : Nat := 380432111575639254326053

theorem tailTrace_833500 : CollatzResearch.WordTrace tailWord_833500 prefixEnd_833500 380432111575639254326053 := by
  unfold tailWord_833500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15200121240189662656004977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20266828320252883541339969 15200121240189662656004977)
  ·
    refine ⟨11400090930142246992003733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15200121240189662656004977 11400090930142246992003733)
    ·
      refine ⟨534379262350417827750175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11400090930142246992003733 534379262350417827750175)
      ·
        refine ⟨801568893525626741625263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534379262350417827750175 801568893525626741625263)
        ·
          refine ⟨1202353340288440112437895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801568893525626741625263 1202353340288440112437895)
          ·
            refine ⟨1803530010432660168656843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202353340288440112437895 1803530010432660168656843)
            ·
              refine ⟨2705295015648990252985265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803530010432660168656843 2705295015648990252985265)
              ·
                refine ⟨2028971261736742689738949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705295015648990252985265 2028971261736742689738949)
                ·
                  refine ⟨380432111575639254326053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028971261736742689738949 380432111575639254326053)
                  ·
                    rfl

theorem cell20_833500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_833500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833500 prefixEnd_833500 := by exact prefixLift 833500
  have htrace : WordTrace (prefixWord ++ tailWord_833500) baseStart_833500 baseEnd_833500 := by
    simpa [prefixWord, tailWord_833500, baseEnd_833500] using wordTrace_append hprefix tailTrace_833500
  have hstable : (prefixWord ++ tailWord_833500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833500).length < 2 ^ (prefixWord ++ tailWord_833500).sum := by decide
  have hdescent : baseEnd_833500 < baseStart_833500 := by decide
  rcases family_descends (prefixWord ++ tailWord_833500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833515 : List Nat := [1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_833515 : Nat := 118140960795 + 833515 * 2 ^ 59
def prefixEnd_833515 : Nat := 4983230072969 + 3 ^ 40 * 833515 * 2
def baseEnd_833515 : Nat := 126812985994788622941997

theorem tailTrace_833515 : CollatzResearch.WordTrace tailWord_833515 prefixEnd_833515 126812985994788622941997 := by
  unfold tailWord_833515
  simp only [CollatzResearch.WordTrace]
  refine ⟨30400789575324982873805999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20267193050216655249203999 30400789575324982873805999)
  ·
    refine ⟨45601184362987474310708999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30400789575324982873805999 45601184362987474310708999)
    ·
      refine ⟨68401776544481211466063499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45601184362987474310708999 68401776544481211466063499)
      ·
        refine ⟨102602664816721817199095249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68401776544481211466063499 102602664816721817199095249)
        ·
          refine ⟨76951998612541362899321437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102602664816721817199095249 76951998612541362899321437)
          ·
            refine ⟨28856999479703011087245539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76951998612541362899321437 28856999479703011087245539)
            ·
              refine ⟨43285499219554516630868309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28856999479703011087245539 43285499219554516630868309)
              ·
                refine ⟨126812985994788622941997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43285499219554516630868309 126812985994788622941997)
                ·
                  rfl

theorem cell20_833515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_833515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833515 prefixEnd_833515 := by exact prefixLift 833515
  have htrace : WordTrace (prefixWord ++ tailWord_833515) baseStart_833515 baseEnd_833515 := by
    simpa [prefixWord, tailWord_833515, baseEnd_833515] using wordTrace_append hprefix tailTrace_833515
  have hstable : (prefixWord ++ tailWord_833515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833515).length < 2 ^ (prefixWord ++ tailWord_833515).sum := by decide
  have hdescent : baseEnd_833515 < baseStart_833515 := by decide
  rcases family_descends (prefixWord ++ tailWord_833515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833521 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 2]
def baseStart_833521 : Nat := 118140960795 + 833521 * 2 ^ 59
def prefixEnd_833521 : Nat := 4983230072969 + 3 ^ 40 * 833521 * 2
def baseEnd_833521 : Nat := 380441696547856514625967

theorem tailTrace_833521 : CollatzResearch.WordTrace tailWord_833521 prefixEnd_833521 380441696547856514625967 := by
  unfold tailWord_833521
  simp only [CollatzResearch.WordTrace]
  refine ⟨30401008413303245898524417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20267338942202163932349611 30401008413303245898524417)
  ·
    refine ⟨22800756309977434423893313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30401008413303245898524417 22800756309977434423893313)
    ·
      refine ⟨17100567232483075817919985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22800756309977434423893313 17100567232483075817919985)
      ·
        refine ⟨12825425424362306863439989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17100567232483075817919985 12825425424362306863439989)
        ·
          refine ⟨1202383633533966268447499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12825425424362306863439989 1202383633533966268447499)
          ·
            refine ⟨1803575450300949402671249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202383633533966268447499 1803575450300949402671249)
            ·
              refine ⟨1352681587725712052003437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803575450300949402671249 1352681587725712052003437)
              ·
                refine ⟨507255595397142019501289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352681587725712052003437 507255595397142019501289)
                ·
                  refine ⟨380441696547856514625967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507255595397142019501289 380441696547856514625967)
                  ·
                    rfl

theorem cell20_833521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_833521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833521 prefixEnd_833521 := by exact prefixLift 833521
  have htrace : WordTrace (prefixWord ++ tailWord_833521) baseStart_833521 baseEnd_833521 := by
    simpa [prefixWord, tailWord_833521, baseEnd_833521] using wordTrace_append hprefix tailTrace_833521
  have hstable : (prefixWord ++ tailWord_833521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833521).length < 2 ^ (prefixWord ++ tailWord_833521).sum := by decide
  have hdescent : baseEnd_833521 < baseStart_833521 := by decide
  rcases family_descends (prefixWord ++ tailWord_833521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833570 : List Nat := [3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_833570 : Nat := 118140960795 + 833570 * 2 ^ 59
def prefixEnd_833570 : Nat := 4983230072969 + 3 ^ 40 * 833570 * 2
def baseEnd_833570 : Nat := 126821353827676707330811

theorem tailTrace_833570 : CollatzResearch.WordTrace tailWord_833570 prefixEnd_833570 126821353827676707330811 := by
  unfold tailWord_833570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600698897531431816764541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20268530393417151511372109 7600698897531431816764541)
  ·
    refine ⟨2850262086574286931286703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7600698897531431816764541 2850262086574286931286703)
    ·
      refine ⟨4275393129861430396930055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850262086574286931286703 4275393129861430396930055)
      ·
        refine ⟨6413089694792145595395083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275393129861430396930055 6413089694792145595395083)
        ·
          refine ⟨9619634542188218393092625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413089694792145595395083 9619634542188218393092625)
          ·
            refine ⟨7214725906641163794819469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9619634542188218393092625 7214725906641163794819469)
            ·
              refine ⟨2705522214990436423057301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7214725906641163794819469 2705522214990436423057301)
              ·
                refine ⟨126821353827676707330811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2705522214990436423057301 126821353827676707330811)
                ·
                  rfl

theorem cell20_833570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_833570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833570 prefixEnd_833570 := by exact prefixLift 833570
  have htrace : WordTrace (prefixWord ++ tailWord_833570) baseStart_833570 baseEnd_833570 := by
    simpa [prefixWord, tailWord_833570, baseEnd_833570] using wordTrace_append hprefix tailTrace_833570
  have hstable : (prefixWord ++ tailWord_833570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833570).length < 2 ^ (prefixWord ++ tailWord_833570).sum := by decide
  have hdescent : baseEnd_833570 < baseStart_833570 := by decide
  rcases family_descends (prefixWord ++ tailWord_833570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833591 : List Nat := [1, 1, 3, 1, 2, 2, 10]
def baseStart_833591 : Nat := 118140960795 + 833591 * 2 ^ 59
def prefixEnd_833591 : Nat := 4983230072969 + 3 ^ 40 * 833591 * 2
def baseEnd_833591 : Nat := 42274849606138598032483

theorem tailTrace_833591 : CollatzResearch.WordTrace tailWord_833591 prefixEnd_833591 42274849606138598032483 := by
  unfold tailWord_833591
  simp only [CollatzResearch.WordTrace]
  refine ⟨30403561523049647853572627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20269041015366431902381751 30403561523049647853572627)
  ·
    refine ⟨45605342284574471780358941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30403561523049647853572627 45605342284574471780358941)
    ·
      refine ⟨17102003356715426917634603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45605342284574471780358941 17102003356715426917634603)
      ·
        refine ⟨25653005035073140376451905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17102003356715426917634603 25653005035073140376451905)
        ·
          refine ⟨19239753776304855282338929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25653005035073140376451905 19239753776304855282338929)
          ·
            refine ⟨14429815332228641461754197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19239753776304855282338929 14429815332228641461754197)
            ·
              refine ⟨42274849606138598032483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14429815332228641461754197 42274849606138598032483)
              ·
                rfl

theorem cell20_833591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_833591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833591 prefixEnd_833591 := by exact prefixLift 833591
  have htrace : WordTrace (prefixWord ++ tailWord_833591) baseStart_833591 baseEnd_833591 := by
    simpa [prefixWord, tailWord_833591, baseEnd_833591] using wordTrace_append hprefix tailTrace_833591
  have hstable : (prefixWord ++ tailWord_833591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833591).length < 2 ^ (prefixWord ++ tailWord_833591).sum := by decide
  have hdescent : baseEnd_833591 < baseStart_833591 := by decide
  rcases family_descends (prefixWord ++ tailWord_833591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833597 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 2]
def baseStart_833597 : Nat := 118140960795 + 833597 * 2 ^ 59
def prefixEnd_833597 : Nat := 4983230072969 + 3 ^ 40 * 833597 * 2
def baseEnd_833597 : Nat := 380476385018738028092323

theorem tailTrace_833597 : CollatzResearch.WordTrace tailWord_833597 prefixEnd_833597 380476385018738028092323 := by
  unfold tailWord_833597
  simp only [CollatzResearch.WordTrace]
  refine ⟨30403780361027910878291045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20269186907351940585527363 30403780361027910878291045)
  ·
    refine ⟨5700708817692733289679571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30403780361027910878291045 5700708817692733289679571)
    ·
      refine ⟨8551063226539099934519357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700708817692733289679571 8551063226539099934519357)
      ·
        refine ⟨3206648709952162475444759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8551063226539099934519357 3206648709952162475444759)
        ·
          refine ⟨4809973064928243713167139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206648709952162475444759 4809973064928243713167139)
          ·
            refine ⟨7214959597392365569750709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809973064928243713167139 7214959597392365569750709)
            ·
              refine ⟨676402462255534272164129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7214959597392365569750709 676402462255534272164129)
              ·
                refine ⟨507301846691650704123097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676402462255534272164129 507301846691650704123097)
                ·
                  refine ⟨380476385018738028092323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507301846691650704123097 380476385018738028092323)
                  ·
                    rfl

theorem cell20_833597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_833597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833597 prefixEnd_833597 := by exact prefixLift 833597
  have htrace : WordTrace (prefixWord ++ tailWord_833597) baseStart_833597 baseEnd_833597 := by
    simpa [prefixWord, tailWord_833597, baseEnd_833597] using wordTrace_append hprefix tailTrace_833597
  have hstable : (prefixWord ++ tailWord_833597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833597).length < 2 ^ (prefixWord ++ tailWord_833597).sum := by decide
  have hdescent : baseEnd_833597 < baseStart_833597 := by decide
  rcases family_descends (prefixWord ++ tailWord_833597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833615 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_833615 : Nat := 118140960795 + 833615 * 2 ^ 59
def prefixEnd_833615 : Nat := 4983230072969 + 3 ^ 40 * 833615 * 2
def baseEnd_833615 : Nat := 380484600709209965492249

theorem tailTrace_833615 : CollatzResearch.WordTrace tailWord_833615 prefixEnd_833615 380484600709209965492249 := by
  unfold tailWord_833615
  simp only [CollatzResearch.WordTrace]
  refine ⟨30404436874962699952446299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20269624583308466634964199 30404436874962699952446299)
  ·
    refine ⟨45606655312444049928669449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30404436874962699952446299 45606655312444049928669449)
    ·
      refine ⟨34204991484333037446502087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45606655312444049928669449 34204991484333037446502087)
      ·
        refine ⟨51307487226499556169753131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34204991484333037446502087 51307487226499556169753131)
        ·
          refine ⟨76961230839749334254629697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51307487226499556169753131 76961230839749334254629697)
          ·
            refine ⟨57720923129812000690972273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76961230839749334254629697 57720923129812000690972273)
            ·
              refine ⟨43290692347359000518229205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57720923129812000690972273 43290692347359000518229205)
              ·
                refine ⟨1014625601891226574645997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43290692347359000518229205 1014625601891226574645997)
                ·
                  refine ⟨380484600709209965492249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014625601891226574645997 380484600709209965492249)
                  ·
                    rfl

theorem cell20_833615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_833615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833615 prefixEnd_833615 := by exact prefixLift 833615
  have htrace : WordTrace (prefixWord ++ tailWord_833615) baseStart_833615 baseEnd_833615 := by
    simpa [prefixWord, tailWord_833615, baseEnd_833615] using wordTrace_append hprefix tailTrace_833615
  have hstable : (prefixWord ++ tailWord_833615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833615).length < 2 ^ (prefixWord ++ tailWord_833615).sum := by decide
  have hdescent : baseEnd_833615 < baseStart_833615 := by decide
  rcases family_descends (prefixWord ++ tailWord_833615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833743 : List Nat := [1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_833743 : Nat := 118140960795 + 833743 * 2 ^ 59
def prefixEnd_833743 : Nat := 4983230072969 + 3 ^ 40 * 833743 * 2
def baseEnd_833743 : Nat := 126847674465670136408353

theorem tailTrace_833743 : CollatzResearch.WordTrace tailWord_833743 prefixEnd_833743 126847674465670136408353 := by
  unfold tailWord_833743
  simp only [CollatzResearch.WordTrace]
  refine ⟨30409105418498977813105883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20272736945665985208737255 30409105418498977813105883)
  ·
    refine ⟨45613658127748466719658825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30409105418498977813105883 45613658127748466719658825)
    ·
      refine ⟨34210243595811350039744119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45613658127748466719658825 34210243595811350039744119)
      ·
        refine ⟨51315365393717025059616179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34210243595811350039744119 51315365393717025059616179)
        ·
          refine ⟨76973048090575537589424269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51315365393717025059616179 76973048090575537589424269)
          ·
            refine ⟨28864893033965826596034101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76973048090575537589424269 28864893033965826596034101)
            ·
              refine ⟨2706083721934296243378197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28864893033965826596034101 2706083721934296243378197)
              ·
                refine ⟨126847674465670136408353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2706083721934296243378197 126847674465670136408353)
                ·
                  rfl

theorem cell20_833743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_833743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833743 prefixEnd_833743 := by exact prefixLift 833743
  have htrace : WordTrace (prefixWord ++ tailWord_833743) baseStart_833743 baseEnd_833743 := by
    simpa [prefixWord, tailWord_833743, baseEnd_833743] using wordTrace_append hprefix tailTrace_833743
  have hstable : (prefixWord ++ tailWord_833743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833743).length < 2 ^ (prefixWord ++ tailWord_833743).sum := by decide
  have hdescent : baseEnd_833743 < baseStart_833743 := by decide
  rcases family_descends (prefixWord ++ tailWord_833743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833756 : List Nat := [2, 2, 5, 2, 1, 2, 6]
def baseStart_833756 : Nat := 118140960795 + 833756 * 2 ^ 59
def prefixEnd_833756 : Nat := 4983230072969 + 3 ^ 40 * 833756 * 2
def baseEnd_833756 : Nat := 42283217439026682421297

theorem tailTrace_833756 : CollatzResearch.WordTrace tailWord_833756 prefixEnd_833756 42283217439026682421297 := by
  unfold tailWord_833756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15204789783725940516664561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20273053044967920688886081 15204789783725940516664561)
  ·
    refine ⟨11403592337794455387498421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15204789783725940516664561 11403592337794455387498421)
    ·
      refine ⟨1069086781668230192577977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11403592337794455387498421 1069086781668230192577977)
      ·
        refine ⟨801815086251172644433483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069086781668230192577977 801815086251172644433483)
        ·
          refine ⟨1202722629376758966650225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801815086251172644433483 1202722629376758966650225)
          ·
            refine ⟨902041972032569224987669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202722629376758966650225 902041972032569224987669)
            ·
              refine ⟨42283217439026682421297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 902041972032569224987669 42283217439026682421297)
              ·
                rfl

theorem cell20_833756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 6].length) (baseStart_833756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833756 prefixEnd_833756 := by exact prefixLift 833756
  have htrace : WordTrace (prefixWord ++ tailWord_833756) baseStart_833756 baseEnd_833756 := by
    simpa [prefixWord, tailWord_833756, baseEnd_833756] using wordTrace_append hprefix tailTrace_833756
  have hstable : (prefixWord ++ tailWord_833756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833756).length < 2 ^ (prefixWord ++ tailWord_833756).sum := by decide
  have hdescent : baseEnd_833756 < baseStart_833756 := by decide
  rcases family_descends (prefixWord ++ tailWord_833756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833762 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_833762 : Nat := 118140960795 + 833762 * 2 ^ 59
def prefixEnd_833762 : Nat := 4983230072969 + 3 ^ 40 * 833762 * 2
def baseEnd_833762 : Nat := 380551695514730787591649

theorem tailTrace_833762 : CollatzResearch.WordTrace tailWord_833762 prefixEnd_833762 380551695514730787591649 := by
  unfold tailWord_833762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602449601357536014511885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20273198936953429372031693 7602449601357536014511885)
  ·
    refine ⟨2850918600509076005441957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7602449601357536014511885 2850918600509076005441957)
    ·
      refine ⟨534547237595451751020367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2850918600509076005441957 534547237595451751020367)
      ·
        refine ⟨801820856393177626530551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534547237595451751020367 801820856393177626530551)
        ·
          refine ⟨1202731284589766439795827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801820856393177626530551 1202731284589766439795827)
          ·
            refine ⟨1804096926884649659693741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202731284589766439795827 1804096926884649659693741)
            ·
              refine ⟨676536347581743622385153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804096926884649659693741 676536347581743622385153)
              ·
                refine ⟨507402260686307716788865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676536347581743622385153 507402260686307716788865)
                ·
                  refine ⟨380551695514730787591649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507402260686307716788865 380551695514730787591649)
                  ·
                    rfl

theorem cell20_833762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_833762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833762 prefixEnd_833762 := by exact prefixLift 833762
  have htrace : WordTrace (prefixWord ++ tailWord_833762) baseStart_833762 baseEnd_833762 := by
    simpa [prefixWord, tailWord_833762, baseEnd_833762] using wordTrace_append hprefix tailTrace_833762
  have hstable : (prefixWord ++ tailWord_833762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833762).length < 2 ^ (prefixWord ++ tailWord_833762).sum := by decide
  have hdescent : baseEnd_833762 < baseStart_833762 := by decide
  rcases family_descends (prefixWord ++ tailWord_833762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833821 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 2]
def baseStart_833821 : Nat := 118140960795 + 833821 * 2 ^ 59
def prefixEnd_833821 : Nat := 4983230072969 + 3 ^ 40 * 833821 * 2
def baseEnd_833821 : Nat := 380578624722388804624741

theorem tailTrace_833821 : CollatzResearch.WordTrace tailWord_833821 prefixEnd_833821 380578624722388804624741 := by
  unfold tailWord_833821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30411950312216397134445317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20274633541477598089630211 30411950312216397134445317)
  ·
    refine ⟨5702240683540574462708497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30411950312216397134445317 5702240683540574462708497)
    ·
      refine ⟨4276680512655430847031373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5702240683540574462708497 4276680512655430847031373)
      ·
        refine ⟨1603755192245786567636765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4276680512655430847031373 1603755192245786567636765)
        ·
          refine ⟨601408197092169962863787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1603755192245786567636765 601408197092169962863787)
          ·
            refine ⟨902112295638254944295681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601408197092169962863787 902112295638254944295681)
            ·
              refine ⟨676584221728691208221761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902112295638254944295681 676584221728691208221761)
              ·
                refine ⟨507438166296518406166321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676584221728691208221761 507438166296518406166321)
                ·
                  refine ⟨380578624722388804624741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507438166296518406166321 380578624722388804624741)
                  ·
                    rfl

theorem cell20_833821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_833821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833821 prefixEnd_833821 := by exact prefixLift 833821
  have htrace : WordTrace (prefixWord ++ tailWord_833821) baseStart_833821 baseEnd_833821 := by
    simpa [prefixWord, tailWord_833821, baseEnd_833821] using wordTrace_append hprefix tailTrace_833821
  have hstable : (prefixWord ++ tailWord_833821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833821).length < 2 ^ (prefixWord ++ tailWord_833821).sum := by decide
  have hdescent : baseEnd_833821 < baseStart_833821 := by decide
  rcases family_descends (prefixWord ++ tailWord_833821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833832 : List Nat := [2, 1, 5, 1, 4, 1, 1, 5]
def baseStart_833832 : Nat := 118140960795 + 833832 * 2 ^ 59
def prefixEnd_833832 : Nat := 4983230072969 + 3 ^ 40 * 833832 * 2
def baseEnd_833832 : Nat := 126861215140707218419343

theorem tailTrace_833832 : CollatzResearch.WordTrace tailWord_833832 prefixEnd_833832 126861215140707218419343 := by
  unfold tailWord_833832
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206175757588273006547875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20274901010117697342063833 15206175757588273006547875)
  ·
    refine ⟨22809263636382409509821813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15206175757588273006547875 22809263636382409509821813)
    ·
      refine ⟨2138368465910850891545795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22809263636382409509821813 2138368465910850891545795)
      ·
        refine ⟨3207552698866276337318693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138368465910850891545795 3207552698866276337318693)
        ·
          refine ⟨601416131037426813247255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3207552698866276337318693 601416131037426813247255)
          ·
            refine ⟨902124196556140219870883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601416131037426813247255 902124196556140219870883)
            ·
              refine ⟨1353186294834210329806325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902124196556140219870883 1353186294834210329806325)
              ·
                refine ⟨126861215140707218419343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1353186294834210329806325 126861215140707218419343)
                ·
                  rfl

theorem cell20_833832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_833832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833832 prefixEnd_833832 := by exact prefixLift 833832
  have htrace : WordTrace (prefixWord ++ tailWord_833832) baseStart_833832 baseEnd_833832 := by
    simpa [prefixWord, tailWord_833832, baseEnd_833832] using wordTrace_append hprefix tailTrace_833832
  have hstable : (prefixWord ++ tailWord_833832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833832).length < 2 ^ (prefixWord ++ tailWord_833832).sum := by decide
  have hdescent : baseEnd_833832 < baseStart_833832 := by decide
  rcases family_descends (prefixWord ++ tailWord_833832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833843 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_833843 : Nat := 118140960795 + 833843 * 2 ^ 59
def prefixEnd_833843 : Nat := 4983230072969 + 3 ^ 40 * 833843 * 2
def baseEnd_833843 : Nat := 380588666121854505891317

theorem tailTrace_833843 : CollatzResearch.WordTrace tailWord_833843 prefixEnd_833843 380588666121854505891317 := by
  unfold tailWord_833843
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412752718136694891746183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20275168478757796594497455 30412752718136694891746183)
  ·
    refine ⟨45619129077205042337619275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30412752718136694891746183 45619129077205042337619275)
    ·
      refine ⟨68428693615807563506428913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45619129077205042337619275 68428693615807563506428913)
      ·
        refine ⟨51321520211855672629821685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68428693615807563506428913 51321520211855672629821685)
        ·
          refine ⟨4811392519861469309045783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51321520211855672629821685 4811392519861469309045783)
          ·
            refine ⟨7217088779792203963568675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811392519861469309045783 7217088779792203963568675)
            ·
              refine ⟨10825633169688305945353013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217088779792203963568675 10825633169688305945353013)
              ·
                refine ⟨1014903109658278682376845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10825633169688305945353013 1014903109658278682376845)
                ·
                  refine ⟨380588666121854505891317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014903109658278682376845 380588666121854505891317)
                  ·
                    rfl

theorem cell20_833843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_833843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833843 prefixEnd_833843 := by exact prefixLift 833843
  have htrace : WordTrace (prefixWord ++ tailWord_833843) baseStart_833843 baseEnd_833843 := by
    simpa [prefixWord, tailWord_833843, baseEnd_833843] using wordTrace_append hprefix tailTrace_833843
  have hstable : (prefixWord ++ tailWord_833843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833843).length < 2 ^ (prefixWord ++ tailWord_833843).sum := by decide
  have hdescent : baseEnd_833843 < baseStart_833843 := by decide
  rcases family_descends (prefixWord ++ tailWord_833843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833850 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_833850 : Nat := 118140960795 + 833850 * 2 ^ 59
def prefixEnd_833850 : Nat := 4983230072969 + 3 ^ 40 * 833850 * 2
def baseEnd_833850 : Nat := 380591861112593592657955

theorem tailTrace_833850 : CollatzResearch.WordTrace tailWord_833850 prefixEnd_833850 380591861112593592657955 := by
  unfold tailWord_833850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7603252007277833771812751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20275338686074223391500669 7603252007277833771812751)
  ·
    refine ⟨11404878010916750657719127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7603252007277833771812751 11404878010916750657719127)
    ·
      refine ⟨17107317016375125986578691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11404878010916750657719127 17107317016375125986578691)
      ·
        refine ⟨25660975524562688979868037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17107317016375125986578691 25660975524562688979868037)
        ·
          refine ⟨4811432910855504183725257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25660975524562688979868037 4811432910855504183725257)
          ·
            refine ⟨3608574683141628137793943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4811432910855504183725257 3608574683141628137793943)
            ·
              refine ⟨5412862024712442206690915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3608574683141628137793943 5412862024712442206690915)
              ·
                refine ⟨8119293037068663310036373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412862024712442206690915 8119293037068663310036373)
                ·
                  refine ⟨380591861112593592657955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8119293037068663310036373 380591861112593592657955)
                  ·
                    rfl

theorem cell20_833850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_833850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833850 prefixEnd_833850 := by exact prefixLift 833850
  have htrace : WordTrace (prefixWord ++ tailWord_833850) baseStart_833850 baseEnd_833850 := by
    simpa [prefixWord, tailWord_833850, baseEnd_833850] using wordTrace_append hprefix tailTrace_833850
  have hstable : (prefixWord ++ tailWord_833850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833850).length < 2 ^ (prefixWord ++ tailWord_833850).sum := by decide
  have hdescent : baseEnd_833850 < baseStart_833850 := by decide
  rcases family_descends (prefixWord ++ tailWord_833850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833877 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 3]
def baseStart_833877 : Nat := 118140960795 + 833877 * 2 ^ 59
def prefixEnd_833877 : Nat := 4983230072969 + 3 ^ 40 * 833877 * 2
def baseEnd_833877 : Nat := 380604184648301498757845

theorem tailTrace_833877 : CollatzResearch.WordTrace tailWord_833877 prefixEnd_833877 380604184648301498757845 := by
  unfold tailWord_833877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30413992800013518698483885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20275995200009012465655923 30413992800013518698483885)
  ·
    refine ⟨11405247300005069511931457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30413992800013518698483885 11405247300005069511931457)
    ·
      refine ⟨8553935475003802133948593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11405247300005069511931457 8553935475003802133948593)
      ·
        refine ⟨6415451606252851600461445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8553935475003802133948593 6415451606252851600461445)
        ·
          refine ⟨1202897176172409675086521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6415451606252851600461445 1202897176172409675086521)
          ·
            refine ⟨902172882129307256314891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202897176172409675086521 902172882129307256314891)
            ·
              refine ⟨1353259323193960884472337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902172882129307256314891 1353259323193960884472337)
              ·
                refine ⟨1014944492395470663354253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353259323193960884472337 1014944492395470663354253)
                ·
                  refine ⟨380604184648301498757845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014944492395470663354253 380604184648301498757845)
                  ·
                    rfl

theorem cell20_833877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_833877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833877 prefixEnd_833877 := by exact prefixLift 833877
  have htrace : WordTrace (prefixWord ++ tailWord_833877) baseStart_833877 baseEnd_833877 := by
    simpa [prefixWord, tailWord_833877, baseEnd_833877] using wordTrace_append hprefix tailTrace_833877
  have hstable : (prefixWord ++ tailWord_833877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833877).length < 2 ^ (prefixWord ++ tailWord_833877).sum := by decide
  have hdescent : baseEnd_833877 < baseStart_833877 := by decide
  rcases family_descends (prefixWord ++ tailWord_833877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833943 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 2]
def baseStart_833943 : Nat := 118140960795 + 833943 * 2 ^ 59
def prefixEnd_833943 : Nat := 4983230072969 + 3 ^ 40 * 833943 * 2
def baseEnd_833943 : Nat := 380634308846698602557575

theorem tailTrace_833943 : CollatzResearch.WordTrace tailWord_833943 prefixEnd_833943 380634308846698602557575 := by
  unfold tailWord_833943
  simp only [CollatzResearch.WordTrace]
  refine ⟨30416400017774411970386483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20277600011849607980257655 30416400017774411970386483)
  ·
    refine ⟨45624600026661617955579725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30416400017774411970386483 45624600026661617955579725)
    ·
      refine ⟨17109225009998106733342397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45624600026661617955579725 17109225009998106733342397)
      ·
        refine ⟨6415959378749290025003399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17109225009998106733342397 6415959378749290025003399)
        ·
          refine ⟨9623939068123935037505099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415959378749290025003399 9623939068123935037505099)
          ·
            refine ⟨14435908602185902556257649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623939068123935037505099 14435908602185902556257649)
            ·
              refine ⟨10826931451639426917193237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435908602185902556257649 10826931451639426917193237)
              ·
                refine ⟨507512411795598136743433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10826931451639426917193237 507512411795598136743433)
                ·
                  refine ⟨380634308846698602557575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507512411795598136743433 380634308846698602557575)
                  ·
                    rfl

theorem cell20_833943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 2].length) (baseStart_833943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833943 prefixEnd_833943 := by exact prefixLift 833943
  have htrace : WordTrace (prefixWord ++ tailWord_833943) baseStart_833943 baseEnd_833943 := by
    simpa [prefixWord, tailWord_833943, baseEnd_833943] using wordTrace_append hprefix tailTrace_833943
  have hstable : (prefixWord ++ tailWord_833943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833943).length < 2 ^ (prefixWord ++ tailWord_833943).sum := by decide
  have hdescent : baseEnd_833943 < baseStart_833943 := by decide
  rcases family_descends (prefixWord ++ tailWord_833943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833953 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 3]
def baseStart_833953 : Nat := 118140960795 + 833953 * 2 ^ 59
def prefixEnd_833953 : Nat := 4983230072969 + 3 ^ 40 * 833953 * 2
def baseEnd_833953 : Nat := 380638873119183012224201

theorem tailTrace_833953 : CollatzResearch.WordTrace tailWord_833953 prefixEnd_833953 380638873119183012224201 := by
  unfold tailWord_833953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30416764747738183678250513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20277843165158789118833675 30416764747738183678250513)
  ·
    refine ⟨22812573560803637758687885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30416764747738183678250513 22812573560803637758687885)
    ·
      refine ⟨8554715085301364159507957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22812573560803637758687885 8554715085301364159507957)
      ·
        refine ⟨802004539247002889953871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8554715085301364159507957 802004539247002889953871)
        ·
          refine ⟨1203006808870504334930807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802004539247002889953871 1203006808870504334930807)
          ·
            refine ⟨1804510213305756502396211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203006808870504334930807 1804510213305756502396211)
            ·
              refine ⟨2706765319958634753594317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804510213305756502396211 2706765319958634753594317)
              ·
                refine ⟨1015036994984488032597869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2706765319958634753594317 1015036994984488032597869)
                ·
                  refine ⟨380638873119183012224201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015036994984488032597869 380638873119183012224201)
                  ·
                    rfl

theorem cell20_833953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_833953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833953 prefixEnd_833953 := by exact prefixLift 833953
  have htrace : WordTrace (prefixWord ++ tailWord_833953) baseStart_833953 baseEnd_833953 := by
    simpa [prefixWord, tailWord_833953, baseEnd_833953] using wordTrace_append hprefix tailTrace_833953
  have hstable : (prefixWord ++ tailWord_833953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833953).length < 2 ^ (prefixWord ++ tailWord_833953).sum := by decide
  have hdescent : baseEnd_833953 < baseStart_833953 := by decide
  rcases family_descends (prefixWord ++ tailWord_833953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833957 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_833957 : Nat := 118140960795 + 833957 * 2 ^ 59
def prefixEnd_833957 : Nat := 4983230072969 + 3 ^ 40 * 833957 * 2
def baseEnd_833957 : Nat := 380640698828176776090851

theorem tailTrace_833957 : CollatzResearch.WordTrace tailWord_833957 prefixEnd_833957 380640698828176776090851 := by
  unfold tailWord_833957
  simp only [CollatzResearch.WordTrace]
  refine ⟨30416910639723692361396125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20277940426482461574264083 30416910639723692361396125)
  ·
    refine ⟨11406341489896384635523547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30416910639723692361396125 11406341489896384635523547)
    ·
      refine ⟨17109512234844576953285321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11406341489896384635523547 17109512234844576953285321)
      ·
        refine ⟨12832134176133432714963991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17109512234844576953285321 12832134176133432714963991)
        ·
          refine ⟨19248201264200149072445987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832134176133432714963991 19248201264200149072445987)
          ·
            refine ⟨28872301896300223608668981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19248201264200149072445987 28872301896300223608668981)
            ·
              refine ⟨2706778302778145963312717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28872301896300223608668981 2706778302778145963312717)
              ·
                refine ⟨1015041863541804736242269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2706778302778145963312717 1015041863541804736242269)
                ·
                  refine ⟨380640698828176776090851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015041863541804736242269 380640698828176776090851)
                  ·
                    rfl

theorem cell20_833957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_833957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833957 prefixEnd_833957 := by exact prefixLift 833957
  have htrace : WordTrace (prefixWord ++ tailWord_833957) baseStart_833957 baseEnd_833957 := by
    simpa [prefixWord, tailWord_833957, baseEnd_833957] using wordTrace_append hprefix tailTrace_833957
  have hstable : (prefixWord ++ tailWord_833957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833957).length < 2 ^ (prefixWord ++ tailWord_833957).sum := by decide
  have hdescent : baseEnd_833957 < baseStart_833957 := by decide
  rcases family_descends (prefixWord ++ tailWord_833957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833978 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_833978 : Nat := 118140960795 + 833978 * 2 ^ 59
def prefixEnd_833978 : Nat := 4983230072969 + 3 ^ 40 * 833978 * 2
def baseEnd_833978 : Nat := 380650283800394036390765

theorem tailTrace_833978 : CollatzResearch.WordTrace tailWord_833978 prefixEnd_833978 380650283800394036390765 := by
  unfold tailWord_833978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604419143161903236977647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20278451048431741965273725 7604419143161903236977647)
  ·
    refine ⟨11406628714742854855466471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7604419143161903236977647 11406628714742854855466471)
    ·
      refine ⟨17109943072114282283199707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11406628714742854855466471 17109943072114282283199707)
      ·
        refine ⟨25664914608171423424799561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17109943072114282283199707 25664914608171423424799561)
        ·
          refine ⟨19248685956128567568599671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25664914608171423424799561 19248685956128567568599671)
          ·
            refine ⟨28873028934192851352899507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19248685956128567568599671 28873028934192851352899507)
            ·
              refine ⟨43309543401289277029349261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28873028934192851352899507 43309543401289277029349261)
              ·
                refine ⟨16241078775483478886005973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43309543401289277029349261 16241078775483478886005973)
                ·
                  refine ⟨380650283800394036390765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16241078775483478886005973 380650283800394036390765)
                  ·
                    rfl

theorem cell20_833978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_833978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833978 prefixEnd_833978 := by exact prefixLift 833978
  have htrace : WordTrace (prefixWord ++ tailWord_833978) baseStart_833978 baseEnd_833978 := by
    simpa [prefixWord, tailWord_833978, baseEnd_833978] using wordTrace_append hprefix tailTrace_833978
  have hstable : (prefixWord ++ tailWord_833978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833978).length < 2 ^ (prefixWord ++ tailWord_833978).sum := by decide
  have hdescent : baseEnd_833978 < baseStart_833978 := by decide
  rcases family_descends (prefixWord ++ tailWord_833978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833988 : List Nat := [2, 3, 3, 2, 2, 8]
def baseStart_833988 : Nat := 118140960795 + 833988 * 2 ^ 59
def prefixEnd_833988 : Nat := 4983230072969 + 3 ^ 40 * 833988 * 2
def baseEnd_833988 : Nat := 14098327706402905409533

theorem tailTrace_833988 : CollatzResearch.WordTrace tailWord_833988 prefixEnd_833988 14098327706402905409533 := by
  unfold tailWord_833988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15209020651305692327887309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20278694201740923103849745 15209020651305692327887309)
  ·
    refine ⟨5703382744239634622957741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15209020651305692327887309 5703382744239634622957741)
    ·
      refine ⟨2138768529089862983609153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5703382744239634622957741 2138768529089862983609153)
      ·
        refine ⟨1604076396817397237706865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138768529089862983609153 1604076396817397237706865)
        ·
          refine ⟨1203057297613047928280149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604076396817397237706865 1203057297613047928280149)
          ·
            refine ⟨14098327706402905409533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1203057297613047928280149 14098327706402905409533)
            ·
              rfl

theorem cell20_833988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 8].length) (baseStart_833988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_833988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_833988 prefixEnd_833988 := by exact prefixLift 833988
  have htrace : WordTrace (prefixWord ++ tailWord_833988) baseStart_833988 baseEnd_833988 := by
    simpa [prefixWord, tailWord_833988, baseEnd_833988] using wordTrace_append hprefix tailTrace_833988
  have hstable : (prefixWord ++ tailWord_833988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833988).length < 2 ^ (prefixWord ++ tailWord_833988).sum := by decide
  have hdescent : baseEnd_833988 < baseStart_833988 := by decide
  rcases family_descends (prefixWord ++ tailWord_833988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834019 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_834019 : Nat := 118140960795 + 834019 * 2 ^ 59
def prefixEnd_834019 : Nat := 4983230072969 + 3 ^ 40 * 834019 * 2
def baseEnd_834019 : Nat := 380668997317580116023931

theorem tailTrace_834019 : CollatzResearch.WordTrace tailWord_834019 prefixEnd_834019 380668997317580116023931 := by
  unfold tailWord_834019
  simp only [CollatzResearch.WordTrace]
  refine ⟨30419171965499076950153111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20279447976999384633435407 30419171965499076950153111)
  ·
    refine ⟨45628757948248615425229667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30419171965499076950153111 45628757948248615425229667)
    ·
      refine ⟨68443136922372923137844501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45628757948248615425229667 68443136922372923137844501)
      ·
        refine ⟨3208272043236230772086461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68443136922372923137844501 3208272043236230772086461)
        ·
          refine ⟨1203102016213586539532423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3208272043236230772086461 1203102016213586539532423)
          ·
            refine ⟨1804653024320379809298635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203102016213586539532423 1804653024320379809298635)
            ·
              refine ⟨2706979536480569713947953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804653024320379809298635 2706979536480569713947953)
              ·
                refine ⟨2030234652360427285460965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706979536480569713947953 2030234652360427285460965)
                ·
                  refine ⟨380668997317580116023931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030234652360427285460965 380668997317580116023931)
                  ·
                    rfl

theorem cell20_834019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_834019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834019 prefixEnd_834019 := by exact prefixLift 834019
  have htrace : WordTrace (prefixWord ++ tailWord_834019) baseStart_834019 baseEnd_834019 := by
    simpa [prefixWord, tailWord_834019, baseEnd_834019] using wordTrace_append hprefix tailTrace_834019
  have hstable : (prefixWord ++ tailWord_834019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834019).length < 2 ^ (prefixWord ++ tailWord_834019).sum := by decide
  have hdescent : baseEnd_834019 < baseStart_834019 := by decide
  rcases family_descends (prefixWord ++ tailWord_834019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834087 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 2]
def baseStart_834087 : Nat := 118140960795 + 834087 * 2 ^ 59
def prefixEnd_834087 : Nat := 4983230072969 + 3 ^ 40 * 834087 * 2
def baseEnd_834087 : Nat := 380700034370474101756987

theorem tailTrace_834087 : CollatzResearch.WordTrace tailWord_834087 prefixEnd_834087 380700034370474101756987 := by
  unfold tailWord_834087
  simp only [CollatzResearch.WordTrace]
  refine ⟨30421652129252724563628515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20281101419501816375752343 30421652129252724563628515)
  ·
    refine ⟨45632478193879086845442773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30421652129252724563628515 45632478193879086845442773)
    ·
      refine ⟨1069511207669041097940065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45632478193879086845442773 1069511207669041097940065)
      ·
        refine ⟨802133405751780823455049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069511207669041097940065 802133405751780823455049)
        ·
          refine ⟨601600054313835617591287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802133405751780823455049 601600054313835617591287)
          ·
            refine ⟨902400081470753426386931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601600054313835617591287 902400081470753426386931)
            ·
              refine ⟨1353600122206130139580397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902400081470753426386931 1353600122206130139580397)
              ·
                refine ⟨507600045827298802342649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1353600122206130139580397 507600045827298802342649)
                ·
                  refine ⟨380700034370474101756987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507600045827298802342649 380700034370474101756987)
                  ·
                    rfl

theorem cell20_834087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 2].length) (baseStart_834087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834087 prefixEnd_834087 := by exact prefixLift 834087
  have htrace : WordTrace (prefixWord ++ tailWord_834087) baseStart_834087 baseEnd_834087 := by
    simpa [prefixWord, tailWord_834087, baseEnd_834087] using wordTrace_append hprefix tailTrace_834087
  have hstable : (prefixWord ++ tailWord_834087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834087).length < 2 ^ (prefixWord ++ tailWord_834087).sum := by decide
  have hdescent : baseEnd_834087 < baseStart_834087 := by decide
  rcases family_descends (prefixWord ++ tailWord_834087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834102 : List Nat := [5, 1, 2, 1, 2, 1, 8]
def baseStart_834102 : Nat := 118140960795 + 834102 * 2 ^ 59
def prefixEnd_834102 : Nat := 4983230072969 + 3 ^ 40 * 834102 * 2
def baseEnd_834102 : Nat := 42300764531022301806325

theorem tailTrace_834102 : CollatzResearch.WordTrace tailWord_834102 prefixEnd_834102 42300764531022301806325 := by
  unfold tailWord_834102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901387451512398882839035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20281466149465588083616373 1901387451512398882839035)
  ·
    refine ⟨2852081177268598324258553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901387451512398882839035 2852081177268598324258553)
    ·
      refine ⟨2139060882951448743193915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852081177268598324258553 2139060882951448743193915)
      ·
        refine ⟨3208591324427173114790873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139060882951448743193915 3208591324427173114790873)
        ·
          refine ⟨2406443493320379836093155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3208591324427173114790873 2406443493320379836093155)
          ·
            refine ⟨3609665239980569754139733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406443493320379836093155 3609665239980569754139733)
            ·
              refine ⟨42300764531022301806325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3609665239980569754139733 42300764531022301806325)
              ·
                rfl

theorem cell20_834102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_834102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834102 prefixEnd_834102 := by exact prefixLift 834102
  have htrace : WordTrace (prefixWord ++ tailWord_834102) baseStart_834102 baseEnd_834102 := by
    simpa [prefixWord, tailWord_834102, baseEnd_834102] using wordTrace_append hprefix tailTrace_834102
  have hstable : (prefixWord ++ tailWord_834102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834102).length < 2 ^ (prefixWord ++ tailWord_834102).sum := by decide
  have hdescent : baseEnd_834102 < baseStart_834102 := by decide
  rcases family_descends (prefixWord ++ tailWord_834102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834109 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_834109 : Nat := 118140960795 + 834109 * 2 ^ 59
def prefixEnd_834109 : Nat := 4983230072969 + 3 ^ 40 * 834109 * 2
def baseEnd_834109 : Nat := 380710075769939803023563

theorem tailTrace_834109 : CollatzResearch.WordTrace tailWord_834109 prefixEnd_834109 380710075769939803023563 := by
  unfold tailWord_834109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422454535173022320929381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20281636356782014880619587 30422454535173022320929381)
  ·
    refine ⟨5704210225344941685174259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30422454535173022320929381 5704210225344941685174259)
    ·
      refine ⟨8556315338017412527761389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704210225344941685174259 8556315338017412527761389)
      ·
        refine ⟨3208618251756529697910521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8556315338017412527761389 3208618251756529697910521)
        ·
          refine ⟨2406463688817397273432891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3208618251756529697910521 2406463688817397273432891)
          ·
            refine ⟨3609695533226095910149337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406463688817397273432891 3609695533226095910149337)
            ·
              refine ⟨2707271649919571932612003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609695533226095910149337 2707271649919571932612003)
              ·
                refine ⟨4060907474879357898918005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707271649919571932612003 4060907474879357898918005)
                ·
                  refine ⟨380710075769939803023563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4060907474879357898918005 380710075769939803023563)
                  ·
                    rfl

theorem cell20_834109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_834109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834109 prefixEnd_834109 := by exact prefixLift 834109
  have htrace : WordTrace (prefixWord ++ tailWord_834109) baseStart_834109 baseEnd_834109 := by
    simpa [prefixWord, tailWord_834109, baseEnd_834109] using wordTrace_append hprefix tailTrace_834109
  have hstable : (prefixWord ++ tailWord_834109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834109).length < 2 ^ (prefixWord ++ tailWord_834109).sum := by decide
  have hdescent : baseEnd_834109 < baseStart_834109 := by decide
  rcases family_descends (prefixWord ++ tailWord_834109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834126 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_834126 : Nat := 118140960795 + 834126 * 2 ^ 59
def prefixEnd_834126 : Nat := 4983230072969 + 3 ^ 40 * 834126 * 2
def baseEnd_834126 : Nat := 380717835033163299456827

theorem tailTrace_834126 : CollatzResearch.WordTrace tailWord_834126 prefixEnd_834126 380717835033163299456827 := by
  unfold tailWord_834126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802884322013929278037279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20282049717407622816198821 3802884322013929278037279)
  ·
    refine ⟨5704326483020893917055919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802884322013929278037279 5704326483020893917055919)
    ·
      refine ⟨8556489724531340875583879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704326483020893917055919 8556489724531340875583879)
      ·
        refine ⟨12834734586797011313375819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556489724531340875583879 12834734586797011313375819)
        ·
          refine ⟨19252101880195516970063729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12834734586797011313375819 19252101880195516970063729)
          ·
            refine ⟨14439076410146637727547797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19252101880195516970063729 14439076410146637727547797)
            ·
              refine ⟨676831706725623643478803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14439076410146637727547797 676831706725623643478803)
              ·
                refine ⟨1015247560088435465218205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676831706725623643478803 1015247560088435465218205)
                ·
                  refine ⟨380717835033163299456827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015247560088435465218205 380717835033163299456827)
                  ·
                    rfl

theorem cell20_834126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_834126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834126 prefixEnd_834126 := by exact prefixLift 834126
  have htrace : WordTrace (prefixWord ++ tailWord_834126) baseStart_834126 baseEnd_834126 := by
    simpa [prefixWord, tailWord_834126, baseEnd_834126] using wordTrace_append hprefix tailTrace_834126
  have hstable : (prefixWord ++ tailWord_834126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834126).length < 2 ^ (prefixWord ++ tailWord_834126).sum := by decide
  have hdescent : baseEnd_834126 < baseStart_834126 := by decide
  rcases family_descends (prefixWord ++ tailWord_834126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834213 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_834213 : Nat := 118140960795 + 834213 * 2 ^ 59
def prefixEnd_834213 : Nat := 4983230072969 + 3 ^ 40 * 834213 * 2
def baseEnd_834213 : Nat := 380757544203777663556471

theorem tailTrace_834213 : CollatzResearch.WordTrace tailWord_834213 prefixEnd_834213 380757544203777663556471 := by
  unfold tailWord_834213
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426247726796248082715293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20284165151197498721810195 30426247726796248082715293)
  ·
    refine ⟨11409842897548593031018235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30426247726796248082715293 11409842897548593031018235)
    ·
      refine ⟨17114764346322889546527353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11409842897548593031018235 17114764346322889546527353)
      ·
        refine ⟨12836073259742167159895515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17114764346322889546527353 12836073259742167159895515)
        ·
          refine ⟨19254109889613250739843273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12836073259742167159895515 19254109889613250739843273)
          ·
            refine ⟨14440582417209938054882455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19254109889613250739843273 14440582417209938054882455)
            ·
              refine ⟨21660873625814907082323683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14440582417209938054882455 21660873625814907082323683)
              ·
                refine ⟨32491310438722360623485525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21660873625814907082323683 32491310438722360623485525)
                ·
                  refine ⟨380757544203777663556471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32491310438722360623485525 380757544203777663556471)
                  ·
                    rfl

theorem cell20_834213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_834213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834213 prefixEnd_834213 := by exact prefixLift 834213
  have htrace : WordTrace (prefixWord ++ tailWord_834213) baseStart_834213 baseEnd_834213 := by
    simpa [prefixWord, tailWord_834213, baseEnd_834213] using wordTrace_append hprefix tailTrace_834213
  have hstable : (prefixWord ++ tailWord_834213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834213).length < 2 ^ (prefixWord ++ tailWord_834213).sum := by decide
  have hdescent : baseEnd_834213 < baseStart_834213 := by decide
  rcases family_descends (prefixWord ++ tailWord_834213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834223 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_834223 : Nat := 118140960795 + 834223 * 2 ^ 59
def prefixEnd_834223 : Nat := 4983230072969 + 3 ^ 40 * 834223 * 2
def baseEnd_834223 : Nat := 380762108476262073223097

theorem tailTrace_834223 : CollatzResearch.WordTrace tailWord_834223 prefixEnd_834223 380762108476262073223097 := by
  unfold tailWord_834223
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426612456760019790579323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20284408304506679860386215 30426612456760019790579323)
  ·
    refine ⟨45639918685140029685868985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30426612456760019790579323 45639918685140029685868985)
    ·
      refine ⟨34229939013855022264401739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45639918685140029685868985 34229939013855022264401739)
      ·
        refine ⟨51344908520782533396602609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34229939013855022264401739 51344908520782533396602609)
        ·
          refine ⟨38508681390586900047451957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51344908520782533396602609 38508681390586900047451957)
          ·
            refine ⟨3610188880367521879448621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38508681390586900047451957 3610188880367521879448621)
            ·
              refine ⟨1353820830137820704793233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3610188880367521879448621 1353820830137820704793233)
              ·
                refine ⟨1015365622603365528594925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353820830137820704793233 1015365622603365528594925)
                ·
                  refine ⟨380762108476262073223097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015365622603365528594925 380762108476262073223097)
                  ·
                    rfl

theorem cell20_834223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_834223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834223 prefixEnd_834223 := by exact prefixLift 834223
  have htrace : WordTrace (prefixWord ++ tailWord_834223) baseStart_834223 baseEnd_834223 := by
    simpa [prefixWord, tailWord_834223, baseEnd_834223] using wordTrace_append hprefix tailTrace_834223
  have hstable : (prefixWord ++ tailWord_834223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834223).length < 2 ^ (prefixWord ++ tailWord_834223).sum := by decide
  have hdescent : baseEnd_834223 < baseStart_834223 := by decide
  rcases family_descends (prefixWord ++ tailWord_834223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834240 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_834240 : Nat := 118140960795 + 834240 * 2 ^ 59
def prefixEnd_834240 : Nat := 4983230072969 + 3 ^ 40 * 834240 * 2
def baseEnd_834240 : Nat := 380769867739485569656361

theorem tailTrace_834240 : CollatzResearch.WordTrace tailWord_834240 prefixEnd_834240 380769867739485569656361 := by
  unfold tailWord_834240
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213616248849215846974087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20284821665132287795965449 15213616248849215846974087)
  ·
    refine ⟨22820424373273823770461131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15213616248849215846974087 22820424373273823770461131)
    ·
      refine ⟨34230636559910735655691697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22820424373273823770461131 34230636559910735655691697)
      ·
        refine ⟨25672977419933051741768773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34230636559910735655691697 25672977419933051741768773)
        ·
          refine ⟨4813683266237447201581645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25672977419933051741768773 4813683266237447201581645)
          ·
            refine ⟨1805131224839042700593117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4813683266237447201581645 1805131224839042700593117)
            ·
              refine ⟨676924209314641012722419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1805131224839042700593117 676924209314641012722419)
              ·
                refine ⟨1015386313971961519083629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676924209314641012722419 1015386313971961519083629)
                ·
                  refine ⟨380769867739485569656361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015386313971961519083629 380769867739485569656361)
                  ·
                    rfl

theorem cell20_834240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_834240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834240 prefixEnd_834240 := by exact prefixLift 834240
  have htrace : WordTrace (prefixWord ++ tailWord_834240) baseStart_834240 baseEnd_834240 := by
    simpa [prefixWord, tailWord_834240, baseEnd_834240] using wordTrace_append hprefix tailTrace_834240
  have hstable : (prefixWord ++ tailWord_834240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834240).length < 2 ^ (prefixWord ++ tailWord_834240).sum := by decide
  have hdescent : baseEnd_834240 < baseStart_834240 := by decide
  rcases family_descends (prefixWord ++ tailWord_834240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834246 : List Nat := [6, 1, 2, 1, 3, 1, 2, 4]
def baseStart_834246 : Nat := 118140960795 + 834246 * 2 ^ 59
def prefixEnd_834246 : Nat := 4983230072969 + 3 ^ 40 * 834246 * 2
def baseEnd_834246 : Nat := 126924202100992071818779

theorem tailTrace_834246 : CollatzResearch.WordTrace tailWord_834246 prefixEnd_834246 126924202100992071818779 := by
  unfold tailWord_834246
  simp only [CollatzResearch.WordTrace]
  refine ⟨950857854239896709958331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20284967557117796479111061 950857854239896709958331)
  ·
    refine ⟨1426286781359845064937497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 950857854239896709958331 1426286781359845064937497)
    ·
      refine ⟨1069715086019883798703123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1426286781359845064937497 1069715086019883798703123)
      ·
        refine ⟨1604572629029825698054685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069715086019883798703123 1604572629029825698054685)
        ·
          refine ⟨601714735886184636770507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1604572629029825698054685 601714735886184636770507)
          ·
            refine ⟨902572103829276955155761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601714735886184636770507 902572103829276955155761)
            ·
              refine ⟨676929077871957716366821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902572103829276955155761 676929077871957716366821)
              ·
                refine ⟨126924202100992071818779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676929077871957716366821 126924202100992071818779)
                ·
                  rfl

theorem cell20_834246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_834246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834246 prefixEnd_834246 := by exact prefixLift 834246
  have htrace : WordTrace (prefixWord ++ tailWord_834246) baseStart_834246 baseEnd_834246 := by
    simpa [prefixWord, tailWord_834246, baseEnd_834246] using wordTrace_append hprefix tailTrace_834246
  have hstable : (prefixWord ++ tailWord_834246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834246).length < 2 ^ (prefixWord ++ tailWord_834246).sum := by decide
  have hdescent : baseEnd_834246 < baseStart_834246 := by decide
  rcases family_descends (prefixWord ++ tailWord_834246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834254 : List Nat := [4, 1, 1, 1, 3, 2, 4, 4]
def baseStart_834254 : Nat := 118140960795 + 834254 * 2 ^ 59
def prefixEnd_834254 : Nat := 4983230072969 + 3 ^ 40 * 834254 * 2
def baseEnd_834254 : Nat := 126925419240321247729879

theorem tailTrace_834254 : CollatzResearch.WordTrace tailWord_834254 prefixEnd_834254 126925419240321247729879 := by
  unfold tailWord_834254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803467889955964010619727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20285162079765141389971877 3803467889955964010619727)
  ·
    refine ⟨5705201834933946015929591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3803467889955964010619727 5705201834933946015929591)
    ·
      refine ⟨8557802752400919023894387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705201834933946015929591 8557802752400919023894387)
      ·
        refine ⟨12836704128601378535841581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8557802752400919023894387 12836704128601378535841581)
        ·
          refine ⟨4813764048225516950940593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12836704128601378535841581 4813764048225516950940593)
          ·
            refine ⟨3610323036169137713205445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813764048225516950940593 3610323036169137713205445)
            ·
              refine ⟨676935569281713321226021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3610323036169137713205445 676935569281713321226021)
              ·
                refine ⟨126925419240321247729879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676935569281713321226021 126925419240321247729879)
                ·
                  rfl

theorem cell20_834254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_834254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834254 prefixEnd_834254 := by exact prefixLift 834254
  have htrace : WordTrace (prefixWord ++ tailWord_834254) baseStart_834254 baseEnd_834254 := by
    simpa [prefixWord, tailWord_834254, baseEnd_834254] using wordTrace_append hprefix tailTrace_834254
  have hstable : (prefixWord ++ tailWord_834254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834254).length < 2 ^ (prefixWord ++ tailWord_834254).sum := by decide
  have hdescent : baseEnd_834254 < baseStart_834254 := by decide
  rcases family_descends (prefixWord ++ tailWord_834254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834260 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 2]
def baseStart_834260 : Nat := 118140960795 + 834260 * 2 ^ 59
def prefixEnd_834260 : Nat := 4983230072969 + 3 ^ 40 * 834260 * 2
def baseEnd_834260 : Nat := 380778996284454388989613

theorem tailTrace_834260 : CollatzResearch.WordTrace tailWord_834260 prefixEnd_834260 380778996284454388989613 := by
  unfold tailWord_834260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213980978812987554838117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20285307971750650073117489 15213980978812987554838117)
  ·
    refine ⟨2852621433527435166532147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15213980978812987554838117 2852621433527435166532147)
    ·
      refine ⟨4278932150291152749798221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852621433527435166532147 4278932150291152749798221)
      ·
        refine ⟨1604599556359182281174333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4278932150291152749798221 1604599556359182281174333)
        ·
          refine ⟨601724833634693355440375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1604599556359182281174333 601724833634693355440375)
          ·
            refine ⟨902587250452040033160563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601724833634693355440375 902587250452040033160563)
            ·
              refine ⟨1353880875678060049740845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902587250452040033160563 1353880875678060049740845)
              ·
                refine ⟨507705328379272518652817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1353880875678060049740845 507705328379272518652817)
                ·
                  refine ⟨380778996284454388989613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507705328379272518652817 380778996284454388989613)
                  ·
                    rfl

theorem cell20_834260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_834260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834260 prefixEnd_834260 := by exact prefixLift 834260
  have htrace : WordTrace (prefixWord ++ tailWord_834260) baseStart_834260 baseEnd_834260 := by
    simpa [prefixWord, tailWord_834260, baseEnd_834260] using wordTrace_append hprefix tailTrace_834260
  have hstable : (prefixWord ++ tailWord_834260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834260).length < 2 ^ (prefixWord ++ tailWord_834260).sum := by decide
  have hdescent : baseEnd_834260 < baseStart_834260 := by decide
  rcases family_descends (prefixWord ++ tailWord_834260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834264 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 2]
def baseStart_834264 : Nat := 118140960795 + 834264 * 2 ^ 59
def prefixEnd_834264 : Nat := 4983230072969 + 3 ^ 40 * 834264 * 2
def baseEnd_834264 : Nat := 380780821993448152856263

theorem tailTrace_834264 : CollatzResearch.WordTrace tailWord_834264 prefixEnd_834264 380780821993448152856263 := by
  unfold tailWord_834264
  simp only [CollatzResearch.WordTrace]
  refine ⟨15214053924805741896410923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20285405233074322528547897 15214053924805741896410923)
  ·
    refine ⟨22821080887208612844616385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15214053924805741896410923 22821080887208612844616385)
    ·
      refine ⟨17115810665406459633462289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22821080887208612844616385 17115810665406459633462289)
      ·
        refine ⟨12836857999054844725096717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17115810665406459633462289 12836857999054844725096717)
        ·
          refine ⟨4813821749645566771911269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12836857999054844725096717 4813821749645566771911269)
          ·
            refine ⟨902591578058543769733363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4813821749645566771911269 902591578058543769733363)
            ·
              refine ⟨1353887367087815654600045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902591578058543769733363 1353887367087815654600045)
              ·
                refine ⟨507707762657930870475017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1353887367087815654600045 507707762657930870475017)
                ·
                  refine ⟨380780821993448152856263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507707762657930870475017 380780821993448152856263)
                  ·
                    rfl

theorem cell20_834264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_834264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834264 prefixEnd_834264 := by exact prefixLift 834264
  have htrace : WordTrace (prefixWord ++ tailWord_834264) baseStart_834264 baseEnd_834264 := by
    simpa [prefixWord, tailWord_834264, baseEnd_834264] using wordTrace_append hprefix tailTrace_834264
  have hstable : (prefixWord ++ tailWord_834264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834264).length < 2 ^ (prefixWord ++ tailWord_834264).sum := by decide
  have hdescent : baseEnd_834264 < baseStart_834264 := by decide
  rcases family_descends (prefixWord ++ tailWord_834264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834275 : List Nat := [1, 1, 1, 7, 1, 1, 8]
def baseStart_834275 : Nat := 118140960795 + 834275 * 2 ^ 59
def prefixEnd_834275 : Nat := 4983230072969 + 3 ^ 40 * 834275 * 2
def baseEnd_834275 : Nat := 42309538077020111498839

theorem tailTrace_834275 : CollatzResearch.WordTrace tailWord_834275 prefixEnd_834275 42309538077020111498839 := by
  unfold tailWord_834275
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428509052571632671472279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20285672701714421780981519 30428509052571632671472279)
  ·
    refine ⟨45642763578857449007208419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30428509052571632671472279 45642763578857449007208419)
    ·
      refine ⟨68464145368286173510812629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45642763578857449007208419 68464145368286173510812629)
      ·
        refine ⟨1604628407069207191659671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 68464145368286173510812629 1604628407069207191659671)
        ·
          refine ⟨2406942610603810787489507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604628407069207191659671 2406942610603810787489507)
          ·
            refine ⟨3610413915905716181234261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406942610603810787489507 3610413915905716181234261)
            ·
              refine ⟨42309538077020111498839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3610413915905716181234261 42309538077020111498839)
              ·
                rfl

theorem cell20_834275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_834275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834275 prefixEnd_834275 := by exact prefixLift 834275
  have htrace : WordTrace (prefixWord ++ tailWord_834275) baseStart_834275 baseEnd_834275 := by
    simpa [prefixWord, tailWord_834275, baseEnd_834275] using wordTrace_append hprefix tailTrace_834275
  have hstable : (prefixWord ++ tailWord_834275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834275).length < 2 ^ (prefixWord ++ tailWord_834275).sum := by decide
  have hdescent : baseEnd_834275 < baseStart_834275 := by decide
  rcases family_descends (prefixWord ++ tailWord_834275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834333 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 3]
def baseStart_834333 : Nat := 118140960795 + 834333 * 2 ^ 59
def prefixEnd_834333 : Nat := 4983230072969 + 3 ^ 40 * 834333 * 2
def baseEnd_834333 : Nat := 380812315473590579555981

theorem tailTrace_834333 : CollatzResearch.WordTrace tailWord_834333 prefixEnd_834333 380812315473590579555981 := by
  unfold tailWord_834333
  simp only [CollatzResearch.WordTrace]
  refine ⟨30430624486361508577083653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20287082990907672384722435 30430624486361508577083653)
  ·
    refine ⟨5705742091192782858203185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30430624486361508577083653 5705742091192782858203185)
    ·
      refine ⟨4279306568394587143652389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5705742091192782858203185 4279306568394587143652389)
      ·
        refine ⟨802369981573985089434823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4279306568394587143652389 802369981573985089434823)
        ·
          refine ⟨1203554972360977634152235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802369981573985089434823 1203554972360977634152235)
          ·
            refine ⟨1805332458541466451228353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203554972360977634152235 1805332458541466451228353)
            ·
              refine ⟨1353999343906099838421265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805332458541466451228353 1353999343906099838421265)
              ·
                refine ⟨1015499507929574878815949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353999343906099838421265 1015499507929574878815949)
                ·
                  refine ⟨380812315473590579555981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015499507929574878815949 380812315473590579555981)
                  ·
                    rfl

theorem cell20_834333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_834333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834333 prefixEnd_834333 := by exact prefixLift 834333
  have htrace : WordTrace (prefixWord ++ tailWord_834333) baseStart_834333 baseEnd_834333 := by
    simpa [prefixWord, tailWord_834333, baseEnd_834333] using wordTrace_append hprefix tailTrace_834333
  have hstable : (prefixWord ++ tailWord_834333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834333).length < 2 ^ (prefixWord ++ tailWord_834333).sum := by decide
  have hdescent : baseEnd_834333 < baseStart_834333 := by decide
  rcases family_descends (prefixWord ++ tailWord_834333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834337 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_834337 : Nat := 118140960795 + 834337 * 2 ^ 59
def prefixEnd_834337 : Nat := 4983230072969 + 3 ^ 40 * 834337 * 2
def baseEnd_834337 : Nat := 380814141182584343422631

theorem tailTrace_834337 : CollatzResearch.WordTrace tailWord_834337 prefixEnd_834337 380814141182584343422631 := by
  unfold tailWord_834337
  simp only [CollatzResearch.WordTrace]
  refine ⟨30430770378347017260229265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20287180252231344840152843 30430770378347017260229265)
  ·
    refine ⟨22823077783760262945171949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30430770378347017260229265 22823077783760262945171949)
    ·
      refine ⟨8558654168910098604439481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22823077783760262945171949 8558654168910098604439481)
      ·
        refine ⟨6418990626682573953329611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8558654168910098604439481 6418990626682573953329611)
        ·
          refine ⟨9628485940023860929994417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418990626682573953329611 9628485940023860929994417)
          ·
            refine ⟨7221364455017895697495813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9628485940023860929994417 7221364455017895697495813)
            ·
              refine ⟨1354005835315855443280465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7221364455017895697495813 1354005835315855443280465)
              ·
                refine ⟨1015504376486891582460349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354005835315855443280465 1015504376486891582460349)
                ·
                  refine ⟨380814141182584343422631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015504376486891582460349 380814141182584343422631)
                  ·
                    rfl

theorem cell20_834337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_834337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834337 prefixEnd_834337 := by exact prefixLift 834337
  have htrace : WordTrace (prefixWord ++ tailWord_834337) baseStart_834337 baseEnd_834337 := by
    simpa [prefixWord, tailWord_834337, baseEnd_834337] using wordTrace_append hprefix tailTrace_834337
  have hstable : (prefixWord ++ tailWord_834337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834337).length < 2 ^ (prefixWord ++ tailWord_834337).sum := by decide
  have hdescent : baseEnd_834337 < baseStart_834337 := by decide
  rcases family_descends (prefixWord ++ tailWord_834337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834340 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 2]
def baseStart_834340 : Nat := 118140960795 + 834340 * 2 ^ 59
def prefixEnd_834340 : Nat := 4983230072969 + 3 ^ 40 * 834340 * 2
def baseEnd_834340 : Nat := 380815510464329666322619

theorem tailTrace_834340 : CollatzResearch.WordTrace tailWord_834340 prefixEnd_834340 380815510464329666322619 := by
  unfold tailWord_834340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15215439898668074386294237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20287253198224099181725649 15215439898668074386294237)
  ·
    refine ⟨5705789962000527894860339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15215439898668074386294237 5705789962000527894860339)
    ·
      refine ⟨8558684943000791842290509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705789962000527894860339 8558684943000791842290509)
      ·
        refine ⟨3209506853625296940858941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8558684943000791842290509 3209506853625296940858941)
        ·
          refine ⟨1203565070109486352822103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3209506853625296940858941 1203565070109486352822103)
          ·
            refine ⟨1805347605164229529233155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203565070109486352822103 1805347605164229529233155)
            ·
              refine ⟨2708021407746344293849733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805347605164229529233155 2708021407746344293849733)
              ·
                refine ⟨507754013952439555096825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2708021407746344293849733 507754013952439555096825)
                ·
                  refine ⟨380815510464329666322619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507754013952439555096825 380815510464329666322619)
                  ·
                    rfl

theorem cell20_834340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_834340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834340 prefixEnd_834340 := by exact prefixLift 834340
  have htrace : WordTrace (prefixWord ++ tailWord_834340) baseStart_834340 baseEnd_834340 := by
    simpa [prefixWord, tailWord_834340, baseEnd_834340] using wordTrace_append hprefix tailTrace_834340
  have hstable : (prefixWord ++ tailWord_834340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834340).length < 2 ^ (prefixWord ++ tailWord_834340).sum := by decide
  have hdescent : baseEnd_834340 < baseStart_834340 := by decide
  rcases family_descends (prefixWord ++ tailWord_834340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834344 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_834344 : Nat := 118140960795 + 834344 * 2 ^ 59
def prefixEnd_834344 : Nat := 4983230072969 + 3 ^ 40 * 834344 * 2
def baseEnd_834344 : Nat := 380817336173323430189269

theorem tailTrace_834344 : CollatzResearch.WordTrace tailWord_834344 prefixEnd_834344 380817336173323430189269 := by
  unfold tailWord_834344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15215512844660828727867043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20287350459547771637156057 15215512844660828727867043)
  ·
    refine ⟨22823269266991243091800565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15215512844660828727867043 22823269266991243091800565)
    ·
      refine ⟨2139681493780429039856303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22823269266991243091800565 2139681493780429039856303)
      ·
        refine ⟨3209522240670643559784455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139681493780429039856303 3209522240670643559784455)
        ·
          refine ⟨4814283361005965339676683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209522240670643559784455 4814283361005965339676683)
          ·
            refine ⟨7221425041508948009515025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814283361005965339676683 7221425041508948009515025)
            ·
              refine ⟨5416068781131711007136269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221425041508948009515025 5416068781131711007136269)
              ·
                refine ⟨2031025792924391627676101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5416068781131711007136269 2031025792924391627676101)
                ·
                  refine ⟨380817336173323430189269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031025792924391627676101 380817336173323430189269)
                  ·
                    rfl

theorem cell20_834344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_834344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834344 prefixEnd_834344 := by exact prefixLift 834344
  have htrace : WordTrace (prefixWord ++ tailWord_834344) baseStart_834344 baseEnd_834344 := by
    simpa [prefixWord, tailWord_834344, baseEnd_834344] using wordTrace_append hprefix tailTrace_834344
  have hstable : (prefixWord ++ tailWord_834344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834344).length < 2 ^ (prefixWord ++ tailWord_834344).sum := by decide
  have hdescent : baseEnd_834344 < baseStart_834344 := by decide
  rcases family_descends (prefixWord ++ tailWord_834344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834374 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_834374 : Nat := 118140960795 + 834374 * 2 ^ 59
def prefixEnd_834374 : Nat := 4983230072969 + 3 ^ 40 * 834374 * 2
def baseEnd_834374 : Nat := 380831028990776659189147

theorem tailTrace_834374 : CollatzResearch.WordTrace tailWord_834374 prefixEnd_834374 380831028990776659189147 := by
  unfold tailWord_834374
  simp only [CollatzResearch.WordTrace]
  refine ⟨951003746225405393103943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20288079919475315052884117 951003746225405393103943)
  ·
    refine ⟨1426505619338108089655915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951003746225405393103943 1426505619338108089655915)
    ·
      refine ⟨2139758429007162134483873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426505619338108089655915 2139758429007162134483873)
      ·
        refine ⟨1604818821755371600862905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2139758429007162134483873 1604818821755371600862905)
        ·
          refine ⟨1203614116316528700647179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604818821755371600862905 1203614116316528700647179)
          ·
            refine ⟨1805421174474793050970769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203614116316528700647179 1805421174474793050970769)
            ·
              refine ⟨1354065880856094788228077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805421174474793050970769 1354065880856094788228077)
              ·
                refine ⟨507774705321035545585529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354065880856094788228077 507774705321035545585529)
                ·
                  refine ⟨380831028990776659189147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507774705321035545585529 380831028990776659189147)
                  ·
                    rfl

theorem cell20_834374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_834374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834374 prefixEnd_834374 := by exact prefixLift 834374
  have htrace : WordTrace (prefixWord ++ tailWord_834374) baseStart_834374 baseEnd_834374 := by
    simpa [prefixWord, tailWord_834374, baseEnd_834374] using wordTrace_append hprefix tailTrace_834374
  have hstable : (prefixWord ++ tailWord_834374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834374).length < 2 ^ (prefixWord ++ tailWord_834374).sum := by decide
  have hdescent : baseEnd_834374 < baseStart_834374 := by decide
  rcases family_descends (prefixWord ++ tailWord_834374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834427 : List Nat := [1, 1, 1, 1, 1, 5, 6, 4]
def baseStart_834427 : Nat := 118140960795 + 834427 * 2 ^ 59
def prefixEnd_834427 : Nat := 4983230072969 + 3 ^ 40 * 834427 * 2
def baseEnd_834427 : Nat := 126951739878314676807421

theorem tailTrace_834427 : CollatzResearch.WordTrace tailWord_834427 prefixEnd_834427 126951739878314676807421 := by
  unfold tailWord_834427
  simp only [CollatzResearch.WordTrace]
  refine ⟨30434052948020962631005535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20289368632013975087337023 30434052948020962631005535)
  ·
    refine ⟨45651079422031443946508303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30434052948020962631005535 45651079422031443946508303)
    ·
      refine ⟨68476619133047165919762455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45651079422031443946508303 68476619133047165919762455)
      ·
        refine ⟨102714928699570748879643683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68476619133047165919762455 102714928699570748879643683)
        ·
          refine ⟨154072393049356123319465525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102714928699570748879643683 154072393049356123319465525)
          ·
            refine ⟨14444286848377136561199893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154072393049356123319465525 14444286848377136561199893)
            ·
              refine ⟨677075946017678276306245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14444286848377136561199893 677075946017678276306245)
              ·
                refine ⟨126951739878314676807421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677075946017678276306245 126951739878314676807421)
                ·
                  rfl

theorem cell20_834427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_834427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834427 prefixEnd_834427 := by exact prefixLift 834427
  have htrace : WordTrace (prefixWord ++ tailWord_834427) baseStart_834427 baseEnd_834427 := by
    simpa [prefixWord, tailWord_834427, baseEnd_834427] using wordTrace_append hprefix tailTrace_834427
  have hstable : (prefixWord ++ tailWord_834427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834427).length < 2 ^ (prefixWord ++ tailWord_834427).sum := by decide
  have hdescent : baseEnd_834427 < baseStart_834427 := by decide
  rcases family_descends (prefixWord ++ tailWord_834427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834437 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 2]
def baseStart_834437 : Nat := 118140960795 + 834437 * 2 ^ 59
def prefixEnd_834437 : Nat := 4983230072969 + 3 ^ 40 * 834437 * 2
def baseEnd_834437 : Nat := 380859783907428440088889

theorem tailTrace_834437 : CollatzResearch.WordTrace tailWord_834437 prefixEnd_834437 380859783907428440088889 := by
  unfold tailWord_834437
  simp only [CollatzResearch.WordTrace]
  refine ⟨30434417677984734338869565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20289611785323156225913043 30434417677984734338869565)
  ·
    refine ⟨11412906629244275377076087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30434417677984734338869565 11412906629244275377076087)
    ·
      refine ⟨17119359943866413065614131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11412906629244275377076087 17119359943866413065614131)
      ·
        refine ⟨25679039915799619598421197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17119359943866413065614131 25679039915799619598421197)
        ·
          refine ⟨9629639968424857349407949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25679039915799619598421197 9629639968424857349407949)
          ·
            refine ⟨3611114988159321506027981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9629639968424857349407949 3611114988159321506027981)
            ·
              refine ⟨1354168120559745564760493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3611114988159321506027981 1354168120559745564760493)
              ·
                refine ⟨507813045209904586785185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354168120559745564760493 507813045209904586785185)
                ·
                  refine ⟨380859783907428440088889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507813045209904586785185 380859783907428440088889)
                  ·
                    rfl

theorem cell20_834437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_834437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834437 prefixEnd_834437 := by exact prefixLift 834437
  have htrace : WordTrace (prefixWord ++ tailWord_834437) baseStart_834437 baseEnd_834437 := by
    simpa [prefixWord, tailWord_834437, baseEnd_834437] using wordTrace_append hprefix tailTrace_834437
  have hstable : (prefixWord ++ tailWord_834437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834437).length < 2 ^ (prefixWord ++ tailWord_834437).sum := by decide
  have hdescent : baseEnd_834437 < baseStart_834437 := by decide
  rcases family_descends (prefixWord ++ tailWord_834437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834465 : List Nat := [1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_834465 : Nat := 118140960795 + 834465 * 2 ^ 59
def prefixEnd_834465 : Nat := 4983230072969 + 3 ^ 40 * 834465 * 2
def baseEnd_834465 : Nat := 126957521290128262385147

theorem tailTrace_834465 : CollatzResearch.WordTrace tailWord_834465 prefixEnd_834465 126957521290128262385147 := by
  unfold tailWord_834465
  simp only [CollatzResearch.WordTrace]
  refine ⟨30435438921883295120888849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20290292614588863413925899 30435438921883295120888849)
  ·
    refine ⟨22826579191412471340666637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30435438921883295120888849 22826579191412471340666637)
    ·
      refine ⟨8559967196779676752749989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22826579191412471340666637 8559967196779676752749989)
      ·
        refine ⟨1604993849396189391140623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8559967196779676752749989 1604993849396189391140623)
        ·
          refine ⟨2407490774094284086710935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604993849396189391140623 2407490774094284086710935)
          ·
            refine ⟨3611236161141426130066403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407490774094284086710935 3611236161141426130066403)
            ·
              refine ⟨5416854241712139195099605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611236161141426130066403 5416854241712139195099605)
              ·
                refine ⟨126957521290128262385147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5416854241712139195099605 126957521290128262385147)
                ·
                  rfl

theorem cell20_834465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_834465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834465 prefixEnd_834465 := by exact prefixLift 834465
  have htrace : WordTrace (prefixWord ++ tailWord_834465) baseStart_834465 baseEnd_834465 := by
    simpa [prefixWord, tailWord_834465, baseEnd_834465] using wordTrace_append hprefix tailTrace_834465
  have hstable : (prefixWord ++ tailWord_834465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834465).length < 2 ^ (prefixWord ++ tailWord_834465).sum := by decide
  have hdescent : baseEnd_834465 < baseStart_834465 := by decide
  rcases family_descends (prefixWord ++ tailWord_834465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834558 : List Nat := [4, 2, 2, 2, 2, 1, 7]
def baseStart_834558 : Nat := 118140960795 + 834558 * 2 ^ 59
def prefixEnd_834558 : Nat := 4983230072969 + 3 ^ 40 * 834558 * 2
def baseEnd_834558 : Nat := 42323890178276644117229

theorem tailTrace_834558 : CollatzResearch.WordTrace tailWord_834558 prefixEnd_834558 42323890178276644117229 := by
  unfold tailWord_834558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804853863818296500503041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20292553940364248002682885 3804853863818296500503041)
  ·
    refine ⟨2853640397863722375377281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3804853863818296500503041 2853640397863722375377281)
    ·
      refine ⟨2140230298397791781532961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2853640397863722375377281 2140230298397791781532961)
      ·
        refine ⟨1605172723798343836149721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2140230298397791781532961 1605172723798343836149721)
        ·
          refine ⟨1203879542848757877112291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605172723798343836149721 1203879542848757877112291)
          ·
            refine ⟨1805819314273136815668437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203879542848757877112291 1805819314273136815668437)
            ·
              refine ⟨42323890178276644117229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1805819314273136815668437 42323890178276644117229)
              ·
                rfl

theorem cell20_834558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 7].length) (baseStart_834558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834558 prefixEnd_834558 := by exact prefixLift 834558
  have htrace : WordTrace (prefixWord ++ tailWord_834558) baseStart_834558 baseEnd_834558 := by
    simpa [prefixWord, tailWord_834558, baseEnd_834558] using wordTrace_append hprefix tailTrace_834558
  have hstable : (prefixWord ++ tailWord_834558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834558).length < 2 ^ (prefixWord ++ tailWord_834558).sum := by decide
  have hdescent : baseEnd_834558 < baseStart_834558 := by decide
  rcases family_descends (prefixWord ++ tailWord_834558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834572 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_834572 : Nat := 118140960795 + 834572 * 2 ^ 59
def prefixEnd_834572 : Nat := 4983230072969 + 3 ^ 40 * 834572 * 2
def baseEnd_834572 : Nat := 380921401585967970588337

theorem tailTrace_834572 : CollatzResearch.WordTrace tailWord_834572 prefixEnd_834572 380921401585967970588337 := by
  unfold tailWord_834572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219670766247826197516985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20292894354997101596689313 15219670766247826197516985)
  ·
    refine ⟨11414753074685869648137739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15219670766247826197516985 11414753074685869648137739)
    ·
      refine ⟨17122129612028804472206609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11414753074685869648137739 17122129612028804472206609)
      ·
        refine ⟨12841597209021603354154957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17122129612028804472206609 12841597209021603354154957)
        ·
          refine ⟨4815598953383101257808109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12841597209021603354154957 4815598953383101257808109)
          ·
            refine ⟨1805849607518662971678041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4815598953383101257808109 1805849607518662971678041)
            ·
              refine ⟨1354387205638997228758531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805849607518662971678041 1354387205638997228758531)
              ·
                refine ⟨2031580808458495843137797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354387205638997228758531 2031580808458495843137797)
                ·
                  refine ⟨380921401585967970588337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031580808458495843137797 380921401585967970588337)
                  ·
                    rfl

theorem cell20_834572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_834572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834572 prefixEnd_834572 := by exact prefixLift 834572
  have htrace : WordTrace (prefixWord ++ tailWord_834572) baseStart_834572 baseEnd_834572 := by
    simpa [prefixWord, tailWord_834572, baseEnd_834572] using wordTrace_append hprefix tailTrace_834572
  have hstable : (prefixWord ++ tailWord_834572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834572).length < 2 ^ (prefixWord ++ tailWord_834572).sum := by decide
  have hdescent : baseEnd_834572 < baseStart_834572 := by decide
  rcases family_descends (prefixWord ++ tailWord_834572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834592 : List Nat := [2, 1, 1, 7, 2, 1, 2, 4]
def baseStart_834592 : Nat := 118140960795 + 834592 * 2 ^ 59
def prefixEnd_834592 : Nat := 4983230072969 + 3 ^ 40 * 834592 * 2
def baseEnd_834592 : Nat := 126976843376978929973863

theorem tailTrace_834592 : CollatzResearch.WordTrace tailWord_834592 prefixEnd_834592 126976843376978929973863 := by
  unfold tailWord_834592
  simp only [CollatzResearch.WordTrace]
  refine ⟨15220035496211597905381015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20293380661615463873841353 15220035496211597905381015)
  ·
    refine ⟨22830053244317396858071523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15220035496211597905381015 22830053244317396858071523)
    ·
      refine ⟨34245079866476095287107285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22830053244317396858071523 34245079866476095287107285)
      ·
        refine ⟨802619059370533483291577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34245079866476095287107285 802619059370533483291577)
        ·
          refine ⟨601964294527900112468683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802619059370533483291577 601964294527900112468683)
          ·
            refine ⟨902946441791850168703025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601964294527900112468683 902946441791850168703025)
            ·
              refine ⟨677209831343887626527269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902946441791850168703025 677209831343887626527269)
              ·
                refine ⟨126976843376978929973863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677209831343887626527269 126976843376978929973863)
                ·
                  rfl

theorem cell20_834592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_834592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834592 prefixEnd_834592 := by exact prefixLift 834592
  have htrace : WordTrace (prefixWord ++ tailWord_834592) baseStart_834592 baseEnd_834592 := by
    simpa [prefixWord, tailWord_834592, baseEnd_834592] using wordTrace_append hprefix tailTrace_834592
  have hstable : (prefixWord ++ tailWord_834592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834592).length < 2 ^ (prefixWord ++ tailWord_834592).sum := by decide
  have hdescent : baseEnd_834592 < baseStart_834592 := by decide
  rcases family_descends (prefixWord ++ tailWord_834592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834596 : List Nat := [2, 3, 1, 4, 1, 1, 4, 4]
def baseStart_834596 : Nat := 118140960795 + 834596 * 2 ^ 59
def prefixEnd_834596 : Nat := 4983230072969 + 3 ^ 40 * 834596 * 2
def baseEnd_834596 : Nat := 126977451946643517929413

theorem tailTrace_834596 : CollatzResearch.WordTrace tailWord_834596 prefixEnd_834596 126977451946643517929413 := by
  unfold tailWord_834596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15220108442204352246953821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20293477922939136329271761 15220108442204352246953821)
  ·
    refine ⟨5707540665826632092607683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15220108442204352246953821 5707540665826632092607683)
    ·
      refine ⟨8561310998739948138911525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5707540665826632092607683 8561310998739948138911525)
      ·
        refine ⟨1605245812263740276045911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8561310998739948138911525 1605245812263740276045911)
        ·
          refine ⟨2407868718395610414068867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605245812263740276045911 2407868718395610414068867)
          ·
            refine ⟨3611803077593415621103301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407868718395610414068867 3611803077593415621103301)
            ·
              refine ⟨677213077048765428956869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3611803077593415621103301 677213077048765428956869)
              ·
                refine ⟨126977451946643517929413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677213077048765428956869 126977451946643517929413)
                ·
                  rfl

theorem cell20_834596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_834596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834596 prefixEnd_834596 := by exact prefixLift 834596
  have htrace : WordTrace (prefixWord ++ tailWord_834596) baseStart_834596 baseEnd_834596 := by
    simpa [prefixWord, tailWord_834596, baseEnd_834596] using wordTrace_append hprefix tailTrace_834596
  have hstable : (prefixWord ++ tailWord_834596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834596).length < 2 ^ (prefixWord ++ tailWord_834596).sum := by decide
  have hdescent : baseEnd_834596 < baseStart_834596 := by decide
  rcases family_descends (prefixWord ++ tailWord_834596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834617 : List Nat := [1, 2, 1, 5, 2, 3, 6]
def baseStart_834617 : Nat := 118140960795 + 834617 * 2 ^ 59
def prefixEnd_834617 : Nat := 4983230072969 + 3 ^ 40 * 834617 * 2
def baseEnd_834617 : Nat := 42326882312460868232017

theorem tailTrace_834617 : CollatzResearch.WordTrace tailWord_834617 prefixEnd_834617 42326882312460868232017 := by
  unfold tailWord_834617
  simp only [CollatzResearch.WordTrace]
  refine ⟨30440982817332625080422105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20293988544888416720281403 30440982817332625080422105)
  ·
    refine ⟨22830737112999468810316579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30440982817332625080422105 22830737112999468810316579)
    ·
      refine ⟨34246105669499203215474869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22830737112999468810316579 34246105669499203215474869)
      ·
        refine ⟨3210572406515550301450769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34246105669499203215474869 3210572406515550301450769)
        ·
          refine ⟨2407929304886662726088077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210572406515550301450769 2407929304886662726088077)
          ·
            refine ⟨902973489332498522283029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2407929304886662726088077 902973489332498522283029)
            ·
              refine ⟨42326882312460868232017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 902973489332498522283029 42326882312460868232017)
              ·
                rfl

theorem cell20_834617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_834617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834617 prefixEnd_834617 := by exact prefixLift 834617
  have htrace : WordTrace (prefixWord ++ tailWord_834617) baseStart_834617 baseEnd_834617 := by
    simpa [prefixWord, tailWord_834617, baseEnd_834617] using wordTrace_append hprefix tailTrace_834617
  have hstable : (prefixWord ++ tailWord_834617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834617).length < 2 ^ (prefixWord ++ tailWord_834617).sum := by decide
  have hdescent : baseEnd_834617 < baseStart_834617 := by decide
  rcases family_descends (prefixWord ++ tailWord_834617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834624 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_834624 : Nat := 118140960795 + 834624 * 2 ^ 59
def prefixEnd_834624 : Nat := 4983230072969 + 3 ^ 40 * 834624 * 2
def baseEnd_834624 : Nat := 380945135802886900854791

theorem tailTrace_834624 : CollatzResearch.WordTrace tailWord_834624 prefixEnd_834624 380945135802886900854791 := by
  unfold tailWord_834624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15220619064153632637963463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20294158752204843517284617 15220619064153632637963463)
  ·
    refine ⟨22830928596230448956945195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15220619064153632637963463 22830928596230448956945195)
    ·
      refine ⟨34246392894345673435417793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22830928596230448956945195 34246392894345673435417793)
      ·
        refine ⟨25684794670759255076563345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34246392894345673435417793 25684794670759255076563345)
        ·
          refine ⟨19263596003069441307422509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25684794670759255076563345 19263596003069441307422509)
          ·
            refine ⟨7223848501151040490283441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19263596003069441307422509 7223848501151040490283441)
            ·
              refine ⟨5417886375863280367712581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223848501151040490283441 5417886375863280367712581)
              ·
                refine ⟨1015853695474365068946109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5417886375863280367712581 1015853695474365068946109)
                ·
                  refine ⟨380945135802886900854791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015853695474365068946109 380945135802886900854791)
                  ·
                    rfl

theorem cell20_834624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_834624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834624 prefixEnd_834624 := by exact prefixLift 834624
  have htrace : WordTrace (prefixWord ++ tailWord_834624) baseStart_834624 baseEnd_834624 := by
    simpa [prefixWord, tailWord_834624, baseEnd_834624] using wordTrace_append hprefix tailTrace_834624
  have hstable : (prefixWord ++ tailWord_834624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834624).length < 2 ^ (prefixWord ++ tailWord_834624).sum := by decide
  have hdescent : baseEnd_834624 < baseStart_834624 := by decide
  rcases family_descends (prefixWord ++ tailWord_834624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834627 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 2]
def baseStart_834627 : Nat := 118140960795 + 834627 * 2 ^ 59
def prefixEnd_834627 : Nat := 4983230072969 + 3 ^ 40 * 834627 * 2
def baseEnd_834627 : Nat := 380946505084632223754779

theorem tailTrace_834627 : CollatzResearch.WordTrace tailWord_834627 prefixEnd_834627 380946505084632223754779 := by
  unfold tailWord_834627
  simp only [CollatzResearch.WordTrace]
  refine ⟨30441347547296396788286135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20294231698197597858857423 30441347547296396788286135)
  ·
    refine ⟨45662021320944595182429203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30441347547296396788286135 45662021320944595182429203)
    ·
      refine ⟨68493031981416892773643805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45662021320944595182429203 68493031981416892773643805)
      ·
        refine ⟨25684886993031334790116427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68493031981416892773643805 25684886993031334790116427)
        ·
          refine ⟨38527330489547002185174641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25684886993031334790116427 38527330489547002185174641)
          ·
            refine ⟨28895497867160251638880981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38527330489547002185174641 28895497867160251638880981)
            ·
              refine ⟨677238231261568397786273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28895497867160251638880981 677238231261568397786273)
              ·
                refine ⟨507928673446176298339705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677238231261568397786273 507928673446176298339705)
                ·
                  refine ⟨380946505084632223754779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507928673446176298339705 380946505084632223754779)
                  ·
                    rfl

theorem cell20_834627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 2].length) (baseStart_834627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834627 prefixEnd_834627 := by exact prefixLift 834627
  have htrace : WordTrace (prefixWord ++ tailWord_834627) baseStart_834627 baseEnd_834627 := by
    simpa [prefixWord, tailWord_834627, baseEnd_834627] using wordTrace_append hprefix tailTrace_834627
  have hstable : (prefixWord ++ tailWord_834627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834627).length < 2 ^ (prefixWord ++ tailWord_834627).sum := by decide
  have hdescent : baseEnd_834627 < baseStart_834627 := by decide
  rcases family_descends (prefixWord ++ tailWord_834627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834637 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 3]
def baseStart_834637 : Nat := 118140960795 + 834637 * 2 ^ 59
def prefixEnd_834637 : Nat := 4983230072969 + 3 ^ 40 * 834637 * 2
def baseEnd_834637 : Nat := 380951069357116633421405

theorem tailTrace_834637 : CollatzResearch.WordTrace tailWord_834637 prefixEnd_834637 380951069357116633421405 := by
  unfold tailWord_834637
  simp only [CollatzResearch.WordTrace]
  refine ⟨30441712277260168496150165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20294474851506778997433443 30441712277260168496150165)
  ·
    refine ⟨1426955262996570398257039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30441712277260168496150165 1426955262996570398257039)
    ·
      refine ⟨2140432894494855597385559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426955262996570398257039 2140432894494855597385559)
      ·
        refine ⟨3210649341742283396078339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140432894494855597385559 3210649341742283396078339)
        ·
          refine ⟨4815974012613425094117509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210649341742283396078339 4815974012613425094117509)
          ·
            refine ⟨902995127365017205147033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4815974012613425094117509 902995127365017205147033)
            ·
              refine ⟨677246345523762903860275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902995127365017205147033 677246345523762903860275)
              ·
                refine ⟨1015869518285644355790413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677246345523762903860275 1015869518285644355790413)
                ·
                  refine ⟨380951069357116633421405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015869518285644355790413 380951069357116633421405)
                  ·
                    rfl

theorem cell20_834637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_834637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834637 prefixEnd_834637 := by exact prefixLift 834637
  have htrace : WordTrace (prefixWord ++ tailWord_834637) baseStart_834637 baseEnd_834637 := by
    simpa [prefixWord, tailWord_834637, baseEnd_834637] using wordTrace_append hprefix tailTrace_834637
  have hstable : (prefixWord ++ tailWord_834637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834637).length < 2 ^ (prefixWord ++ tailWord_834637).sum := by decide
  have hdescent : baseEnd_834637 < baseStart_834637 := by decide
  rcases family_descends (prefixWord ++ tailWord_834637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834641 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 3]
def baseStart_834641 : Nat := 118140960795 + 834641 * 2 ^ 59
def prefixEnd_834641 : Nat := 4983230072969 + 3 ^ 40 * 834641 * 2
def baseEnd_834641 : Nat := 380952895066110397288055

theorem tailTrace_834641 : CollatzResearch.WordTrace tailWord_834641 prefixEnd_834641 380952895066110397288055 := by
  unfold tailWord_834641
  simp only [CollatzResearch.WordTrace]
  refine ⟨30441858169245677179295777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20294572112830451452863851 30441858169245677179295777)
  ·
    refine ⟨22831393626934257884471833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30441858169245677179295777 22831393626934257884471833)
    ·
      refine ⟨17123545220200693413353875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22831393626934257884471833 17123545220200693413353875)
      ·
        refine ⟨25685317830301040120030813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17123545220200693413353875 25685317830301040120030813)
        ·
          refine ⟨9631994186362890045011555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25685317830301040120030813 9631994186362890045011555)
          ·
            refine ⟨14447991279544335067517333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631994186362890045011555 14447991279544335067517333)
            ·
              refine ⟨677249591228640706289875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14447991279544335067517333 677249591228640706289875)
              ·
                refine ⟨1015874386842961059434813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677249591228640706289875 1015874386842961059434813)
                ·
                  refine ⟨380952895066110397288055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015874386842961059434813 380952895066110397288055)
                  ·
                    rfl

theorem cell20_834641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_834641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834641 prefixEnd_834641 := by exact prefixLift 834641
  have htrace : WordTrace (prefixWord ++ tailWord_834641) baseStart_834641 baseEnd_834641 := by
    simpa [prefixWord, tailWord_834641, baseEnd_834641] using wordTrace_append hprefix tailTrace_834641
  have hstable : (prefixWord ++ tailWord_834641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834641).length < 2 ^ (prefixWord ++ tailWord_834641).sum := by decide
  have hdescent : baseEnd_834641 < baseStart_834641 := by decide
  rcases family_descends (prefixWord ++ tailWord_834641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834683 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_834683 : Nat := 118140960795 + 834683 * 2 ^ 59
def prefixEnd_834683 : Nat := 4983230072969 + 3 ^ 40 * 834683 * 2
def baseEnd_834683 : Nat := 380972065010544917887883

theorem tailTrace_834683 : CollatzResearch.WordTrace tailWord_834683 prefixEnd_834683 380972065010544917887883 := by
  unfold tailWord_834683
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443390035093518352324703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20295593356729012234883135 30443390035093518352324703)
  ·
    refine ⟨45665085052640277528487055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30443390035093518352324703 45665085052640277528487055)
    ·
      refine ⟨68497627578960416292730583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45665085052640277528487055 68497627578960416292730583)
      ·
        refine ⟨102746441368440624439095875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68497627578960416292730583 102746441368440624439095875)
        ·
          refine ⟨154119662052660936658643813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102746441368440624439095875 154119662052660936658643813)
          ·
            refine ⟨28897436634873925623495715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154119662052660936658643813 28897436634873925623495715)
            ·
              refine ⟨43346154952310888435243573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28897436634873925623495715 43346154952310888435243573)
              ·
                refine ⟨4063702026779145790804085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43346154952310888435243573 4063702026779145790804085)
                ·
                  refine ⟨380972065010544917887883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063702026779145790804085 380972065010544917887883)
                  ·
                    rfl

theorem cell20_834683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_834683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834683 prefixEnd_834683 := by exact prefixLift 834683
  have htrace : WordTrace (prefixWord ++ tailWord_834683) baseStart_834683 baseEnd_834683 := by
    simpa [prefixWord, tailWord_834683, baseEnd_834683] using wordTrace_append hprefix tailTrace_834683
  have hstable : (prefixWord ++ tailWord_834683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834683).length < 2 ^ (prefixWord ++ tailWord_834683).sum := by decide
  have hdescent : baseEnd_834683 < baseStart_834683 := by decide
  rcases family_descends (prefixWord ++ tailWord_834683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834738 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_834738 : Nat := 118140960795 + 834738 * 2 ^ 59
def prefixEnd_834738 : Nat := 4983230072969 + 3 ^ 40 * 834738 * 2
def baseEnd_834738 : Nat := 380997168509209171054325

theorem tailTrace_834738 : CollatzResearch.WordTrace tailWord_834738 prefixEnd_834738 380997168509209171054325 := by
  unfold tailWord_834738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7611349012473565686394217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20296930699929508497051245 7611349012473565686394217)
  ·
    refine ⟨5708511759355174264795663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7611349012473565686394217 5708511759355174264795663)
    ·
      refine ⟨8562767639032761397193495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5708511759355174264795663 8562767639032761397193495)
      ·
        refine ⟨12844151458549142095790243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562767639032761397193495 12844151458549142095790243)
        ·
          refine ⟨19266227187823713143685365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12844151458549142095790243 19266227187823713143685365)
          ·
            refine ⟨1806208798858473107220503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19266227187823713143685365 1806208798858473107220503)
            ·
              refine ⟨2709313198287709660830755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806208798858473107220503 2709313198287709660830755)
              ·
                refine ⟨4063969797431564491246133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709313198287709660830755 4063969797431564491246133)
                ·
                  refine ⟨380997168509209171054325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063969797431564491246133 380997168509209171054325)
                  ·
                    rfl

theorem cell20_834738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_834738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834738 prefixEnd_834738 := by exact prefixLift 834738
  have htrace : WordTrace (prefixWord ++ tailWord_834738) baseStart_834738 baseEnd_834738 := by
    simpa [prefixWord, tailWord_834738, baseEnd_834738] using wordTrace_append hprefix tailTrace_834738
  have hstable : (prefixWord ++ tailWord_834738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834738).length < 2 ^ (prefixWord ++ tailWord_834738).sum := by decide
  have hdescent : baseEnd_834738 < baseStart_834738 := by decide
  rcases family_descends (prefixWord ++ tailWord_834738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834745 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_834745 : Nat := 118140960795 + 834745 * 2 ^ 59
def prefixEnd_834745 : Nat := 4983230072969 + 3 ^ 40 * 834745 * 2
def baseEnd_834745 : Nat := 381000363499948257820963

theorem tailTrace_834745 : CollatzResearch.WordTrace tailWord_834745 prefixEnd_834745 381000363499948257820963 := by
  unfold tailWord_834745
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445651360868902941081689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20297100907245935294054459 30445651360868902941081689)
  ·
    refine ⟨22834238520651677205811267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30445651360868902941081689 22834238520651677205811267)
    ·
      refine ⟨34251357780977515808716901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22834238520651677205811267 34251357780977515808716901)
      ·
        refine ⟨6422129583933284214134419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34251357780977515808716901 6422129583933284214134419)
        ·
          refine ⟨9633194375899926321201629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422129583933284214134419 9633194375899926321201629)
          ·
            refine ⟨3612447890962472370450611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9633194375899926321201629 3612447890962472370450611)
            ·
              refine ⟨5418671836443708555675917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612447890962472370450611 5418671836443708555675917)
              ·
                refine ⟨2032001938666390708378469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5418671836443708555675917 2032001938666390708378469)
                ·
                  refine ⟨381000363499948257820963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2032001938666390708378469 381000363499948257820963)
                  ·
                    rfl

theorem cell20_834745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_834745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834745 prefixEnd_834745 := by exact prefixLift 834745
  have htrace : WordTrace (prefixWord ++ tailWord_834745) baseStart_834745 baseEnd_834745 := by
    simpa [prefixWord, tailWord_834745, baseEnd_834745] using wordTrace_append hprefix tailTrace_834745
  have hstable : (prefixWord ++ tailWord_834745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834745).length < 2 ^ (prefixWord ++ tailWord_834745).sum := by decide
  have hdescent : baseEnd_834745 < baseStart_834745 := by decide
  rcases family_descends (prefixWord ++ tailWord_834745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834765 : List Nat := [1, 6, 2, 2, 1, 1, 1, 6]
def baseStart_834765 : Nat := 118140960795 + 834765 * 2 ^ 59
def prefixEnd_834765 : Nat := 4983230072969 + 3 ^ 40 * 834765 * 2
def baseEnd_834765 : Nat := 127003164014972359051405

theorem tailTrace_834765 : CollatzResearch.WordTrace tailWord_834765 prefixEnd_834765 127003164014972359051405 := by
  unfold tailWord_834765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30446380820796446356809749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20297587213864297571206499 30446380820796446356809749)
  ·
    refine ⟨1427174100974833422975457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30446380820796446356809749 1427174100974833422975457)
    ·
      refine ⟨1070380575731125067231593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427174100974833422975457 1070380575731125067231593)
      ·
        refine ⟨802785431798343800423695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070380575731125067231593 802785431798343800423695)
        ·
          refine ⟨1204178147697515700635543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802785431798343800423695 1204178147697515700635543)
          ·
            refine ⟨1806267221546273550953315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204178147697515700635543 1806267221546273550953315)
            ·
              refine ⟨2709400832319410326429973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806267221546273550953315 2709400832319410326429973)
              ·
                refine ⟨127003164014972359051405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2709400832319410326429973 127003164014972359051405)
                ·
                  rfl

theorem cell20_834765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_834765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834765 prefixEnd_834765 := by exact prefixLift 834765
  have htrace : WordTrace (prefixWord ++ tailWord_834765) baseStart_834765 baseEnd_834765 := by
    simpa [prefixWord, tailWord_834765, baseEnd_834765] using wordTrace_append hprefix tailTrace_834765
  have hstable : (prefixWord ++ tailWord_834765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834765).length < 2 ^ (prefixWord ++ tailWord_834765).sum := by decide
  have hdescent : baseEnd_834765 < baseStart_834765 := by decide
  rcases family_descends (prefixWord ++ tailWord_834765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834828 : List Nat := [2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_834828 : Nat := 118140960795 + 834828 * 2 ^ 59
def prefixEnd_834828 : Nat := 4983230072969 + 3 ^ 40 * 834828 * 2
def baseEnd_834828 : Nat := 127012748987189619351319

theorem tailTrace_834828 : CollatzResearch.WordTrace tailWord_834828 prefixEnd_834828 127012748987189619351319 := by
  unfold tailWord_834828
  simp only [CollatzResearch.WordTrace]
  refine ⟨15224339309784104058176569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20299119079712138744235425 15224339309784104058176569)
  ·
    refine ⟨11418254482338078043632427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15224339309784104058176569 11418254482338078043632427)
    ·
      refine ⟨17127381723507117065448641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11418254482338078043632427 17127381723507117065448641)
      ·
        refine ⟨12845536292630337799086481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17127381723507117065448641 12845536292630337799086481)
        ·
          refine ⟨9634152219472753349314861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12845536292630337799086481 9634152219472753349314861)
          ·
            refine ⟨3612807082302282505993073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9634152219472753349314861 3612807082302282505993073)
            ·
              refine ⟨2709605311726711879494805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612807082302282505993073 2709605311726711879494805)
              ·
                refine ⟨127012748987189619351319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2709605311726711879494805 127012748987189619351319)
                ·
                  rfl

theorem cell20_834828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_834828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834828 prefixEnd_834828 := by exact prefixLift 834828
  have htrace : WordTrace (prefixWord ++ tailWord_834828) baseStart_834828 baseEnd_834828 := by
    simpa [prefixWord, tailWord_834828, baseEnd_834828] using wordTrace_append hprefix tailTrace_834828
  have hstable : (prefixWord ++ tailWord_834828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834828).length < 2 ^ (prefixWord ++ tailWord_834828).sum := by decide
  have hdescent : baseEnd_834828 < baseStart_834828 := by decide
  rcases family_descends (prefixWord ++ tailWord_834828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834914 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_834914 : Nat := 118140960795 + 834914 * 2 ^ 59
def prefixEnd_834914 : Nat := 4983230072969 + 3 ^ 40 * 834914 * 2
def baseEnd_834914 : Nat := 381077499704934781186939

theorem tailTrace_834914 : CollatzResearch.WordTrace tailWord_834914 prefixEnd_834914 381077499704934781186939 := by
  unfold tailWord_834914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612953824314161200995949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20301210198171096535989197 7612953824314161200995949)
  ·
    refine ⟨2854857684117810450373481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7612953824314161200995949 2854857684117810450373481)
    ·
      refine ⟨2141143263088357837780111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2854857684117810450373481 2141143263088357837780111)
      ·
        refine ⟨3211714894632536756670167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141143263088357837780111 3211714894632536756670167)
        ·
          refine ⟨4817572341948805135005251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211714894632536756670167 4817572341948805135005251)
          ·
            refine ⟨7226358512923207702507877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817572341948805135005251 7226358512923207702507877)
            ·
              refine ⟨1354942221173101444220227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7226358512923207702507877 1354942221173101444220227)
              ·
                refine ⟨2032413331759652166330341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354942221173101444220227 2032413331759652166330341)
                ·
                  refine ⟨381077499704934781186939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2032413331759652166330341 381077499704934781186939)
                  ·
                    rfl

theorem cell20_834914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_834914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834914 prefixEnd_834914 := by exact prefixLift 834914
  have htrace : WordTrace (prefixWord ++ tailWord_834914) baseStart_834914 baseEnd_834914 := by
    simpa [prefixWord, tailWord_834914, baseEnd_834914] using wordTrace_append hprefix tailTrace_834914
  have hstable : (prefixWord ++ tailWord_834914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834914).length < 2 ^ (prefixWord ++ tailWord_834914).sum := by decide
  have hdescent : baseEnd_834914 < baseStart_834914 := by decide
  rcases family_descends (prefixWord ++ tailWord_834914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834949 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_834949 : Nat := 118140960795 + 834949 * 2 ^ 59
def prefixEnd_834949 : Nat := 4983230072969 + 3 ^ 40 * 834949 * 2
def baseEnd_834949 : Nat := 381093474658630215020129

theorem tailTrace_834949 : CollatzResearch.WordTrace tailWord_834949 prefixEnd_834949 381093474658630215020129 := by
  unfold tailWord_834949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453091852129845781507901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20302061234753230521005267 30453091852129845781507901)
  ·
    refine ⟨11419909444548692168065463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30453091852129845781507901 11419909444548692168065463)
    ·
      refine ⟨17129864166823038252098195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11419909444548692168065463 17129864166823038252098195)
      ·
        refine ⟨25694796250234557378147293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17129864166823038252098195 25694796250234557378147293)
        ·
          refine ⟨9635548593837959016805235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25694796250234557378147293 9635548593837959016805235)
          ·
            refine ⟨14453322890756938525207853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9635548593837959016805235 14453322890756938525207853)
            ·
              refine ⟨5419996084033851946952945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14453322890756938525207853 5419996084033851946952945)
              ·
                refine ⟨4064997063025388960214709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419996084033851946952945 4064997063025388960214709)
                ·
                  refine ⟨381093474658630215020129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064997063025388960214709 381093474658630215020129)
                  ·
                    rfl

theorem cell20_834949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_834949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834949 prefixEnd_834949 := by exact prefixLift 834949
  have htrace : WordTrace (prefixWord ++ tailWord_834949) baseStart_834949 baseEnd_834949 := by
    simpa [prefixWord, tailWord_834949, baseEnd_834949] using wordTrace_append hprefix tailTrace_834949
  have hstable : (prefixWord ++ tailWord_834949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834949).length < 2 ^ (prefixWord ++ tailWord_834949).sum := by decide
  have hdescent : baseEnd_834949 < baseStart_834949 := by decide
  rcases family_descends (prefixWord ++ tailWord_834949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834969 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 2]
def baseStart_834969 : Nat := 118140960795 + 834969 * 2 ^ 59
def prefixEnd_834969 : Nat := 4983230072969 + 3 ^ 40 * 834969 * 2
def baseEnd_834969 : Nat := 381102603203599034353381

theorem tailTrace_834969 : CollatzResearch.WordTrace tailWord_834969 prefixEnd_834969 381102603203599034353381 := by
  unfold tailWord_834969
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453821312057389197235961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20302547541371592798157307 30453821312057389197235961)
  ·
    refine ⟨22840365984043041897926971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30453821312057389197235961 22840365984043041897926971)
    ·
      refine ⟨34260548976064562846890457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22840365984043041897926971 34260548976064562846890457)
      ·
        refine ⟨25695411732048422135167843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34260548976064562846890457 25695411732048422135167843)
        ·
          refine ⟨38543117598072633202751765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25695411732048422135167843 38543117598072633202751765)
          ·
            refine ⟨1806708637409654681378989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38543117598072633202751765 1806708637409654681378989)
            ·
              refine ⟨677515739028620505517121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1806708637409654681378989 677515739028620505517121)
              ·
                refine ⟨508136804271465379137841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677515739028620505517121 508136804271465379137841)
                ·
                  refine ⟨381102603203599034353381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508136804271465379137841 381102603203599034353381)
                  ·
                    rfl

theorem cell20_834969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_834969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_834969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_834969 prefixEnd_834969 := by exact prefixLift 834969
  have htrace : WordTrace (prefixWord ++ tailWord_834969) baseStart_834969 baseEnd_834969 := by
    simpa [prefixWord, tailWord_834969, baseEnd_834969] using wordTrace_append hprefix tailTrace_834969
  have hstable : (prefixWord ++ tailWord_834969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834969).length < 2 ^ (prefixWord ++ tailWord_834969).sum := by decide
  have hdescent : baseEnd_834969 < baseStart_834969 := by decide
  rcases family_descends (prefixWord ++ tailWord_834969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835010 : List Nat := [3, 5, 2, 1, 2, 7]
def baseStart_835010 : Nat := 118140960795 + 835010 * 2 ^ 59
def prefixEnd_835010 : Nat := 4983230072969 + 3 ^ 40 * 835010 * 2
def baseEnd_835010 : Nat := 14115604322992041258761

theorem tailTrace_835010 : CollatzResearch.WordTrace tailWord_835010 prefixEnd_835010 14115604322992041258761 := by
  unfold tailWord_835010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7613829176227213299869621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20303544469939235466318989 7613829176227213299869621)
  ·
    refine ⟨713796485271301246862777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7613829176227213299869621 713796485271301246862777)
    ·
      refine ⟨535347363953475935147083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 713796485271301246862777 535347363953475935147083)
      ·
        refine ⟨803021045930213902720625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535347363953475935147083 803021045930213902720625)
        ·
          refine ⟨602265784447660427040469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803021045930213902720625 602265784447660427040469)
          ·
            refine ⟨14115604322992041258761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 602265784447660427040469 14115604322992041258761)
            ·
              rfl

theorem cell20_835010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 7].length) (baseStart_835010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835010 prefixEnd_835010 := by exact prefixLift 835010
  have htrace : WordTrace (prefixWord ++ tailWord_835010) baseStart_835010 baseEnd_835010 := by
    simpa [prefixWord, tailWord_835010, baseEnd_835010] using wordTrace_append hprefix tailTrace_835010
  have hstable : (prefixWord ++ tailWord_835010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835010).length < 2 ^ (prefixWord ++ tailWord_835010).sum := by decide
  have hdescent : baseEnd_835010 < baseStart_835010 := by decide
  rcases family_descends (prefixWord ++ tailWord_835010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835066 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_835066 : Nat := 118140960795 + 835066 * 2 ^ 59
def prefixEnd_835066 : Nat := 4983230072969 + 3 ^ 40 * 835066 * 2
def baseEnd_835066 : Nat := 381146876646697808119651

theorem tailTrace_835066 : CollatzResearch.WordTrace tailWord_835066 prefixEnd_835066 381146876646697808119651 := by
  unfold tailWord_835066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614339798176493690879263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20304906128470649842344701 7614339798176493690879263)
  ·
    refine ⟨11421509697264740536318895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7614339798176493690879263 11421509697264740536318895)
    ·
      refine ⟨17132264545897110804478343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11421509697264740536318895 17132264545897110804478343)
      ·
        refine ⟨25698396818845666206717515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17132264545897110804478343 25698396818845666206717515)
        ·
          refine ⟨38547595228268499310076273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25698396818845666206717515 38547595228268499310076273)
          ·
            refine ⟨28910696421201374482557205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38547595228268499310076273 28910696421201374482557205)
            ·
              refine ⟨1355188894743814428869869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28910696421201374482557205 1355188894743814428869869)
              ·
                refine ⟨508195835528930410826201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355188894743814428869869 508195835528930410826201)
                ·
                  refine ⟨381146876646697808119651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508195835528930410826201 381146876646697808119651)
                  ·
                    rfl

theorem cell20_835066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_835066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835066 prefixEnd_835066 := by exact prefixLift 835066
  have htrace : WordTrace (prefixWord ++ tailWord_835066) baseStart_835066 baseEnd_835066 := by
    simpa [prefixWord, tailWord_835066, baseEnd_835066] using wordTrace_append hprefix tailTrace_835066
  have hstable : (prefixWord ++ tailWord_835066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835066).length < 2 ^ (prefixWord ++ tailWord_835066).sum := by decide
  have hdescent : baseEnd_835066 < baseStart_835066 := by decide
  rcases family_descends (prefixWord ++ tailWord_835066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835076 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_835076 : Nat := 118140960795 + 835076 * 2 ^ 59
def prefixEnd_835076 : Nat := 4983230072969 + 3 ^ 40 * 835076 * 2
def baseEnd_835076 : Nat := 381151440919182217786277

theorem tailTrace_835076 : CollatzResearch.WordTrace tailWord_835076 prefixEnd_835076 381151440919182217786277 := by
  unfold tailWord_835076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228861961334873235690541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20305149281779830980920721 15228861961334873235690541)
  ·
    refine ⟨5710823235500577463383953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15228861961334873235690541 5710823235500577463383953)
    ·
      refine ⟨4283117426625433097537965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5710823235500577463383953 4283117426625433097537965)
      ·
        refine ⟨1606169034984537411576737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4283117426625433097537965 1606169034984537411576737)
        ·
          refine ⟨1204626776238403058682553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1606169034984537411576737 1204626776238403058682553)
          ·
            refine ⟨903470082178802294011915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204626776238403058682553 903470082178802294011915)
            ·
              refine ⟨1355205123268203441017873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903470082178802294011915 1355205123268203441017873)
              ·
                refine ⟨1016403842451152580763405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355205123268203441017873 1016403842451152580763405)
                ·
                  refine ⟨381151440919182217786277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016403842451152580763405 381151440919182217786277)
                  ·
                    rfl

theorem cell20_835076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_835076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835076 prefixEnd_835076 := by exact prefixLift 835076
  have htrace : WordTrace (prefixWord ++ tailWord_835076) baseStart_835076 baseEnd_835076 := by
    simpa [prefixWord, tailWord_835076, baseEnd_835076] using wordTrace_append hprefix tailTrace_835076
  have hstable : (prefixWord ++ tailWord_835076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835076).length < 2 ^ (prefixWord ++ tailWord_835076).sum := by decide
  have hdescent : baseEnd_835076 < baseStart_835076 := by decide
  rcases family_descends (prefixWord ++ tailWord_835076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835080 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_835080 : Nat := 118140960795 + 835080 * 2 ^ 59
def prefixEnd_835080 : Nat := 4983230072969 + 3 ^ 40 * 835080 * 2
def baseEnd_835080 : Nat := 381153266628175981652927

theorem tailTrace_835080 : CollatzResearch.WordTrace tailWord_835080 prefixEnd_835080 381153266628175981652927 := by
  unfold tailWord_835080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228934907327627577263347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20305246543103503436351129 15228934907327627577263347)
  ·
    refine ⟨22843402360991441365895021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15228934907327627577263347 22843402360991441365895021)
    ·
      refine ⟨8566275885371790512210633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22843402360991441365895021 8566275885371790512210633)
      ·
        refine ⟨6424706914028842884157975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8566275885371790512210633 6424706914028842884157975)
        ·
          refine ⟨9637060371043264326236963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424706914028842884157975 9637060371043264326236963)
          ·
            refine ⟨14455590556564896489355445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9637060371043264326236963 14455590556564896489355445)
            ·
              refine ⟨1355211614677959045877073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14455590556564896489355445 1355211614677959045877073)
              ·
                refine ⟨1016408711008469284407805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355211614677959045877073 1016408711008469284407805)
                ·
                  refine ⟨381153266628175981652927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016408711008469284407805 381153266628175981652927)
                  ·
                    rfl

theorem cell20_835080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_835080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835080 prefixEnd_835080 := by exact prefixLift 835080
  have htrace : WordTrace (prefixWord ++ tailWord_835080) baseStart_835080 baseEnd_835080 := by
    simpa [prefixWord, tailWord_835080, baseEnd_835080] using wordTrace_append hprefix tailTrace_835080
  have hstable : (prefixWord ++ tailWord_835080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835080).length < 2 ^ (prefixWord ++ tailWord_835080).sum := by decide
  have hdescent : baseEnd_835080 < baseStart_835080 := by decide
  rcases family_descends (prefixWord ++ tailWord_835080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835118 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_835118 : Nat := 118140960795 + 835118 * 2 ^ 59
def prefixEnd_835118 : Nat := 4983230072969 + 3 ^ 40 * 835118 * 2
def baseEnd_835118 : Nat := 381170610863616738386105

theorem tailTrace_835118 : CollatzResearch.WordTrace tailWord_835118 prefixEnd_835118 381170610863616738386105 := by
  unfold tailWord_835118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807406973564698455551251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20306170525678391762940005 3807406973564698455551251)
  ·
    refine ⟨5711110460347047683326877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3807406973564698455551251 5711110460347047683326877)
    ·
      refine ⟨2141666422630142881247579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5711110460347047683326877 2141666422630142881247579)
      ·
        refine ⟨3212499633945214321871369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141666422630142881247579 3212499633945214321871369)
        ·
          refine ⟨2409374725458910741403527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3212499633945214321871369 2409374725458910741403527)
          ·
            refine ⟨3614062088188366112105291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409374725458910741403527 3614062088188366112105291)
            ·
              refine ⟨5421093132282549168157937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614062088188366112105291 5421093132282549168157937)
              ·
                refine ⟨4065819849211911876118453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5421093132282549168157937 4065819849211911876118453)
                ·
                  refine ⟨381170610863616738386105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4065819849211911876118453 381170610863616738386105)
                  ·
                    rfl

theorem cell20_835118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_835118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835118 prefixEnd_835118 := by exact prefixLift 835118
  have htrace : WordTrace (prefixWord ++ tailWord_835118) baseStart_835118 baseEnd_835118 := by
    simpa [prefixWord, tailWord_835118, baseEnd_835118] using wordTrace_append hprefix tailTrace_835118
  have hstable : (prefixWord ++ tailWord_835118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835118).length < 2 ^ (prefixWord ++ tailWord_835118).sum := by decide
  have hdescent : baseEnd_835118 < baseStart_835118 := by decide
  rcases family_descends (prefixWord ++ tailWord_835118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835156 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_835156 : Nat := 118140960795 + 835156 * 2 ^ 59
def prefixEnd_835156 : Nat := 4983230072969 + 3 ^ 40 * 835156 * 2
def baseEnd_835156 : Nat := 381187955099057495119283

theorem tailTrace_835156 : CollatzResearch.WordTrace tailWord_835156 prefixEnd_835156 381187955099057495119283 := by
  unfold tailWord_835156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15230320881189960067146661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20307094508253280089528881 15230320881189960067146661)
  ·
    refine ⟨2855685165223117512589999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15230320881189960067146661 2855685165223117512589999)
    ·
      refine ⟨4283527747834676268884999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855685165223117512589999 4283527747834676268884999)
      ·
        refine ⟨6425291621752014403327499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283527747834676268884999 6425291621752014403327499)
        ·
          refine ⟨9637937432628021604991249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6425291621752014403327499 9637937432628021604991249)
          ·
            refine ⟨7228453074471016203743437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9637937432628021604991249 7228453074471016203743437)
            ·
              refine ⟨2710669902926631076403789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7228453074471016203743437 2710669902926631076403789)
              ·
                refine ⟨1016501213597486653651421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2710669902926631076403789 1016501213597486653651421)
                ·
                  refine ⟨381187955099057495119283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016501213597486653651421 381187955099057495119283)
                  ·
                    rfl

theorem cell20_835156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_835156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835156 prefixEnd_835156 := by exact prefixLift 835156
  have htrace : WordTrace (prefixWord ++ tailWord_835156) baseStart_835156 baseEnd_835156 := by
    simpa [prefixWord, tailWord_835156, baseEnd_835156] using wordTrace_append hprefix tailTrace_835156
  have hstable : (prefixWord ++ tailWord_835156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835156).length < 2 ^ (prefixWord ++ tailWord_835156).sum := by decide
  have hdescent : baseEnd_835156 < baseStart_835156 := by decide
  rcases family_descends (prefixWord ++ tailWord_835156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835197 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 2]
def baseStart_835197 : Nat := 118140960795 + 835197 * 2 ^ 59
def prefixEnd_835197 : Nat := 4983230072969 + 3 ^ 40 * 835197 * 2
def baseEnd_835197 : Nat := 381206668616243574752449

theorem tailTrace_835197 : CollatzResearch.WordTrace tailWord_835197 prefixEnd_835197 381206668616243574752449 := by
  unfold tailWord_835197
  simp only [CollatzResearch.WordTrace]
  refine ⟨30462137155231384136535845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20308091436820922757690563 30462137155231384136535845)
  ·
    refine ⟨5711650716605884525600471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30462137155231384136535845 5711650716605884525600471)
    ·
      refine ⟨8567476074908826788400707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711650716605884525600471 8567476074908826788400707)
      ·
        refine ⟨12851214112363240182601061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8567476074908826788400707 12851214112363240182601061)
        ·
          refine ⟨2409602646068107534237699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12851214112363240182601061 2409602646068107534237699)
          ·
            refine ⟨3614403969102161301356549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409602646068107534237699 3614403969102161301356549)
            ·
              refine ⟨677700744206655244004353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3614403969102161301356549 677700744206655244004353)
              ·
                refine ⟨508275558154991433003265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677700744206655244004353 508275558154991433003265)
                ·
                  refine ⟨381206668616243574752449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508275558154991433003265 381206668616243574752449)
                  ·
                    rfl

theorem cell20_835197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_835197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835197 prefixEnd_835197 := by exact prefixLift 835197
  have htrace : WordTrace (prefixWord ++ tailWord_835197) baseStart_835197 baseEnd_835197 := by
    simpa [prefixWord, tailWord_835197, baseEnd_835197] using wordTrace_append hprefix tailTrace_835197
  have hstable : (prefixWord ++ tailWord_835197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835197).length < 2 ^ (prefixWord ++ tailWord_835197).sum := by decide
  have hdescent : baseEnd_835197 < baseStart_835197 := by decide
  rcases family_descends (prefixWord ++ tailWord_835197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835204 : List Nat := [2, 3, 2, 1, 5, 1, 1, 5]
def baseStart_835204 : Nat := 118140960795 + 835204 * 2 ^ 59
def prefixEnd_835204 : Nat := 4983230072969 + 3 ^ 40 * 835204 * 2
def baseEnd_835204 : Nat := 127069954535660887173029

theorem tailTrace_835204 : CollatzResearch.WordTrace tailWord_835204 prefixEnd_835204 127069954535660887173029 := by
  unfold tailWord_835204
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231196233103012166020333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20308261644137349554693777 15231196233103012166020333)
  ·
    refine ⟨5711698587413629562257625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15231196233103012166020333 5711698587413629562257625)
    ·
      refine ⟨4283773940560222171693219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5711698587413629562257625 4283773940560222171693219)
      ·
        refine ⟨6425660910840333257539829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283773940560222171693219 6425660910840333257539829)
        ·
          refine ⟨602405710391281242894359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6425660910840333257539829 602405710391281242894359)
          ·
            refine ⟨903608565586921864341539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602405710391281242894359 903608565586921864341539)
            ·
              refine ⟨1355412848380382796512309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903608565586921864341539 1355412848380382796512309)
              ·
                refine ⟨127069954535660887173029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1355412848380382796512309 127069954535660887173029)
                ·
                  rfl

theorem cell20_835204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_835204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835204 prefixEnd_835204 := by exact prefixLift 835204
  have htrace : WordTrace (prefixWord ++ tailWord_835204) baseStart_835204 baseEnd_835204 := by
    simpa [prefixWord, tailWord_835204, baseEnd_835204] using wordTrace_append hprefix tailTrace_835204
  have hstable : (prefixWord ++ tailWord_835204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835204).length < 2 ^ (prefixWord ++ tailWord_835204).sum := by decide
  have hdescent : baseEnd_835204 < baseStart_835204 := by decide
  rcases family_descends (prefixWord ++ tailWord_835204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835218 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_835218 : Nat := 118140960795 + 835218 * 2 ^ 59
def prefixEnd_835218 : Nat := 4983230072969 + 3 ^ 40 * 835218 * 2
def baseEnd_835218 : Nat := 381216253588460835052363

theorem tailTrace_835218 : CollatzResearch.WordTrace tailWord_835218 prefixEnd_835218 381216253588460835052363 := by
  unfold tailWord_835218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615725772038826180762577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20308602058770203148700205 7615725772038826180762577)
  ·
    refine ⟨5711794329029119635571933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7615725772038826180762577 5711794329029119635571933)
    ·
      refine ⟨2141922873385919863339475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5711794329029119635571933 2141922873385919863339475)
      ·
        refine ⟨3212884310078879795009213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141922873385919863339475 3212884310078879795009213)
        ·
          refine ⟨1204831616279579923128455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3212884310078879795009213 1204831616279579923128455)
          ·
            refine ⟨1807247424419369884692683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204831616279579923128455 1807247424419369884692683)
            ·
              refine ⟨2710871136629054827039025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807247424419369884692683 2710871136629054827039025)
              ·
                refine ⟨2033153352471791120279269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710871136629054827039025 2033153352471791120279269)
                ·
                  refine ⟨381216253588460835052363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033153352471791120279269 381216253588460835052363)
                  ·
                    rfl

theorem cell20_835218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_835218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835218 prefixEnd_835218 := by exact prefixLift 835218
  have htrace : WordTrace (prefixWord ++ tailWord_835218) baseStart_835218 baseEnd_835218 := by
    simpa [prefixWord, tailWord_835218, baseEnd_835218] using wordTrace_append hprefix tailTrace_835218
  have hstable : (prefixWord ++ tailWord_835218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835218).length < 2 ^ (prefixWord ++ tailWord_835218).sum := by decide
  have hdescent : baseEnd_835218 < baseStart_835218 := by decide
  rcases family_descends (prefixWord ++ tailWord_835218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835286 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_835286 : Nat := 118140960795 + 835286 * 2 ^ 59
def prefixEnd_835286 : Nat := 4983230072969 + 3 ^ 40 * 835286 * 2
def baseEnd_835286 : Nat := 381247290641354820785419

theorem tailTrace_835286 : CollatzResearch.WordTrace tailWord_835286 prefixEnd_835286 381247290641354820785419 := by
  unfold tailWord_835286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904086453244309521032857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20310255501272634891017141 1904086453244309521032857)
  ·
    refine ⟨1428064839933232140774643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1904086453244309521032857 1428064839933232140774643)
    ·
      refine ⟨2142097259899848211161965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428064839933232140774643 2142097259899848211161965)
      ·
        refine ⟨803286472462443079185737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2142097259899848211161965 803286472462443079185737)
        ·
          refine ⟨602464854346832309389303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803286472462443079185737 602464854346832309389303)
          ·
            refine ⟨903697281520248464083955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602464854346832309389303 903697281520248464083955)
            ·
              refine ⟨1355545922280372696125933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903697281520248464083955 1355545922280372696125933)
              ·
                refine ⟨508329720855139761047225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355545922280372696125933 508329720855139761047225)
                ·
                  refine ⟨381247290641354820785419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508329720855139761047225 381247290641354820785419)
                  ·
                    rfl

theorem cell20_835286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_835286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835286 prefixEnd_835286 := by exact prefixLift 835286
  have htrace : WordTrace (prefixWord ++ tailWord_835286) baseStart_835286 baseEnd_835286 := by
    simpa [prefixWord, tailWord_835286, baseEnd_835286] using wordTrace_append hprefix tailTrace_835286
  have hstable : (prefixWord ++ tailWord_835286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835286).length < 2 ^ (prefixWord ++ tailWord_835286).sum := by decide
  have hdescent : baseEnd_835286 < baseStart_835286 := by decide
  rcases family_descends (prefixWord ++ tailWord_835286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835315 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 2]
def baseStart_835315 : Nat := 118140960795 + 835315 * 2 ^ 59
def prefixEnd_835315 : Nat := 4983230072969 + 3 ^ 40 * 835315 * 2
def baseEnd_835315 : Nat := 381260527031559608818633

theorem tailTrace_835315 : CollatzResearch.WordTrace tailWord_835315 prefixEnd_835315 381260527031559608818633 := by
  unfold tailWord_835315
  simp only [CollatzResearch.WordTrace]
  refine ⟨30466440968803890289331399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20310960645869260192887599 30466440968803890289331399)
  ·
    refine ⟨45699661453205835433997099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30466440968803890289331399 45699661453205835433997099)
    ·
      refine ⟨68549492179808753150995649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45699661453205835433997099 68549492179808753150995649)
      ·
        refine ⟨51412119134856564863246737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68549492179808753150995649 51412119134856564863246737)
        ·
          refine ⟨38559089351142423647435053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51412119134856564863246737 38559089351142423647435053)
          ·
            refine ⟨14459658506678408867788145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38559089351142423647435053 14459658506678408867788145)
            ·
              refine ⟨10844743880008806650841109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14459658506678408867788145 10844743880008806650841109)
              ·
                refine ⟨508347369375412811758177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10844743880008806650841109 508347369375412811758177)
                ·
                  refine ⟨381260527031559608818633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508347369375412811758177 381260527031559608818633)
                  ·
                    rfl

theorem cell20_835315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 2].length) (baseStart_835315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835315 prefixEnd_835315 := by exact prefixLift 835315
  have htrace : WordTrace (prefixWord ++ tailWord_835315) baseStart_835315 baseEnd_835315 := by
    simpa [prefixWord, tailWord_835315, baseEnd_835315] using wordTrace_append hprefix tailTrace_835315
  have hstable : (prefixWord ++ tailWord_835315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835315).length < 2 ^ (prefixWord ++ tailWord_835315).sum := by decide
  have hdescent : baseEnd_835315 < baseStart_835315 := by decide
  rcases family_descends (prefixWord ++ tailWord_835315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835336 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_835336 : Nat := 118140960795 + 835336 * 2 ^ 59
def prefixEnd_835336 : Nat := 4983230072969 + 3 ^ 40 * 835336 * 2
def baseEnd_835336 : Nat := 381270112003776869118547

theorem tailTrace_835336 : CollatzResearch.WordTrace tailWord_835336 prefixEnd_835336 381270112003776869118547 := by
  unfold tailWord_835336
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233603450863905437922931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20311471267818540583897241 15233603450863905437922931)
  ·
    refine ⟨22850405176295858156884397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233603450863905437922931 22850405176295858156884397)
    ·
      refine ⟨8568901941110946808831649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22850405176295858156884397 8568901941110946808831649)
      ·
        refine ⟨6426676455833210106623737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8568901941110946808831649 6426676455833210106623737)
        ·
          refine ⟨4820007341874907579967803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6426676455833210106623737 4820007341874907579967803)
          ·
            refine ⟨7230011012812361369951705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820007341874907579967803 7230011012812361369951705)
            ·
              refine ⟨5422508259609271027463779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7230011012812361369951705 5422508259609271027463779)
              ·
                refine ⟨8133762389413906541195669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422508259609271027463779 8133762389413906541195669)
                ·
                  refine ⟨381270112003776869118547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8133762389413906541195669 381270112003776869118547)
                  ·
                    rfl

theorem cell20_835336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_835336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835336 prefixEnd_835336 := by exact prefixLift 835336
  have htrace : WordTrace (prefixWord ++ tailWord_835336) baseStart_835336 baseEnd_835336 := by
    simpa [prefixWord, tailWord_835336, baseEnd_835336] using wordTrace_append hprefix tailTrace_835336
  have hstable : (prefixWord ++ tailWord_835336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835336).length < 2 ^ (prefixWord ++ tailWord_835336).sum := by decide
  have hdescent : baseEnd_835336 < baseStart_835336 := by decide
  rcases family_descends (prefixWord ++ tailWord_835336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835391 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_835391 : Nat := 118140960795 + 835391 * 2 ^ 59
def prefixEnd_835391 : Nat := 4983230072969 + 3 ^ 40 * 835391 * 2
def baseEnd_835391 : Nat := 381295215502441122284989

theorem tailTrace_835391 : CollatzResearch.WordTrace tailWord_835391 prefixEnd_835391 381295215502441122284989 := by
  unfold tailWord_835391
  simp only [CollatzResearch.WordTrace]
  refine ⟨30469212916528555269098027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20312808611019036846065351 30469212916528555269098027)
  ·
    refine ⟨45703819374792832903647041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30469212916528555269098027 45703819374792832903647041)
    ·
      refine ⟨34277864531094624677735281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45703819374792832903647041 34277864531094624677735281)
      ·
        refine ⟨25708398398320968508301461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34277864531094624677735281 25708398398320968508301461)
        ·
          refine ⟨1205081174921295398826631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25708398398320968508301461 1205081174921295398826631)
          ·
            refine ⟨1807621762381943098239947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205081174921295398826631 1807621762381943098239947)
            ·
              refine ⟨2711432643572914647359921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807621762381943098239947 2711432643572914647359921)
              ·
                refine ⟨2033574482679685985519941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711432643572914647359921 2033574482679685985519941)
                ·
                  refine ⟨381295215502441122284989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033574482679685985519941 381295215502441122284989)
                  ·
                    rfl

theorem cell20_835391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_835391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835391 prefixEnd_835391 := by exact prefixLift 835391
  have htrace : WordTrace (prefixWord ++ tailWord_835391) baseStart_835391 baseEnd_835391 := by
    simpa [prefixWord, tailWord_835391, baseEnd_835391] using wordTrace_append hprefix tailTrace_835391
  have hstable : (prefixWord ++ tailWord_835391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835391).length < 2 ^ (prefixWord ++ tailWord_835391).sum := by decide
  have hdescent : baseEnd_835391 < baseStart_835391 := by decide
  rcases family_descends (prefixWord ++ tailWord_835391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835450 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_835450 : Nat := 118140960795 + 835450 * 2 ^ 59
def prefixEnd_835450 : Nat := 4983230072969 + 3 ^ 40 * 835450 * 2
def baseEnd_835450 : Nat := 381322144710099139318081

theorem tailTrace_835450 : CollatzResearch.WordTrace tailWord_835450 prefixEnd_835450 381322144710099139318081 := by
  unfold tailWord_835450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7617841205828702086373951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20314243215543205563663869 7617841205828702086373951)
  ·
    refine ⟨11426761808743053129560927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7617841205828702086373951 11426761808743053129560927)
    ·
      refine ⟨17140142713114579694341391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11426761808743053129560927 17140142713114579694341391)
      ·
        refine ⟨25710214069671869541512087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17140142713114579694341391 25710214069671869541512087)
        ·
          refine ⟨38565321104507804312268131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25710214069671869541512087 38565321104507804312268131)
          ·
            refine ⟨57847981656761706468402197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38565321104507804312268131 57847981656761706468402197)
            ·
              refine ⟨2711624140160704990706353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57847981656761706468402197 2711624140160704990706353)
              ·
                refine ⟨2033718105120528743029765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711624140160704990706353 2033718105120528743029765)
                ·
                  refine ⟨381322144710099139318081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033718105120528743029765 381322144710099139318081)
                  ·
                    rfl

theorem cell20_835450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_835450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835450 prefixEnd_835450 := by exact prefixLift 835450
  have htrace : WordTrace (prefixWord ++ tailWord_835450) baseStart_835450 baseEnd_835450 := by
    simpa [prefixWord, tailWord_835450, baseEnd_835450] using wordTrace_append hprefix tailTrace_835450
  have hstable : (prefixWord ++ tailWord_835450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835450).length < 2 ^ (prefixWord ++ tailWord_835450).sum := by decide
  have hdescent : baseEnd_835450 < baseStart_835450 := by decide
  rcases family_descends (prefixWord ++ tailWord_835450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835463 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 2]
def baseStart_835463 : Nat := 118140960795 + 835463 * 2 ^ 59
def prefixEnd_835463 : Nat := 4983230072969 + 3 ^ 40 * 835463 * 2
def baseEnd_835463 : Nat := 381328078264328871884695

theorem tailTrace_835463 : CollatzResearch.WordTrace tailWord_835463 prefixEnd_835463 381328078264328871884695 := by
  unfold tailWord_835463
  simp only [CollatzResearch.WordTrace]
  refine ⟨30471838972267711565719043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20314559314845141043812695 30471838972267711565719043)
  ·
    refine ⟨45707758458401567348578565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30471838972267711565719043 45707758458401567348578565)
    ·
      refine ⟨8570204710950293877858481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45707758458401567348578565 8570204710950293877858481)
      ·
        refine ⟨6427653533212720408393861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8570204710950293877858481 6427653533212720408393861)
        ·
          refine ⟨1205185037477385076573849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6427653533212720408393861 1205185037477385076573849)
          ·
            refine ⟨903888778108038807430387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1205185037477385076573849 903888778108038807430387)
            ·
              refine ⟨1355833167162058211145581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903888778108038807430387 1355833167162058211145581)
              ·
                refine ⟨508437437685771829179593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355833167162058211145581 508437437685771829179593)
                ·
                  refine ⟨381328078264328871884695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508437437685771829179593 381328078264328871884695)
                  ·
                    rfl

theorem cell20_835463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 2].length) (baseStart_835463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835463 prefixEnd_835463 := by exact prefixLift 835463
  have htrace : WordTrace (prefixWord ++ tailWord_835463) baseStart_835463 baseEnd_835463 := by
    simpa [prefixWord, tailWord_835463, baseEnd_835463] using wordTrace_append hprefix tailTrace_835463
  have hstable : (prefixWord ++ tailWord_835463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835463).length < 2 ^ (prefixWord ++ tailWord_835463).sum := by decide
  have hdescent : baseEnd_835463 < baseStart_835463 := by decide
  rcases family_descends (prefixWord ++ tailWord_835463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835470 : List Nat := [4, 1, 1, 5, 2, 1, 6]
def baseStart_835470 : Nat := 118140960795 + 835470 * 2 ^ 59
def prefixEnd_835470 : Nat := 4983230072969 + 3 ^ 40 * 835470 * 2
def baseEnd_835470 : Nat := 42370141472785328739037

theorem tailTrace_835470 : CollatzResearch.WordTrace tailWord_835470 prefixEnd_835470 42370141472785328739037 := by
  unfold tailWord_835470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809011785405293970152983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20314729522161567840815909 3809011785405293970152983)
  ·
    refine ⟨5713517678107940955229475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3809011785405293970152983 5713517678107940955229475)
    ·
      refine ⟨8570276517161911432844213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5713517678107940955229475 8570276517161911432844213)
      ·
        refine ⟨803463423483929196829145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8570276517161911432844213 803463423483929196829145)
        ·
          refine ⟨602597567612946897621859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803463423483929196829145 602597567612946897621859)
          ·
            refine ⟨903896351419420346432789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602597567612946897621859 903896351419420346432789)
            ·
              refine ⟨42370141472785328739037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 903896351419420346432789 42370141472785328739037)
              ·
                rfl

theorem cell20_835470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 6].length) (baseStart_835470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835470 prefixEnd_835470 := by exact prefixLift 835470
  have htrace : WordTrace (prefixWord ++ tailWord_835470) baseStart_835470 baseEnd_835470 := by
    simpa [prefixWord, tailWord_835470, baseEnd_835470] using wordTrace_append hprefix tailTrace_835470
  have hstable : (prefixWord ++ tailWord_835470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835470).length < 2 ^ (prefixWord ++ tailWord_835470).sum := by decide
  have hdescent : baseEnd_835470 < baseStart_835470 := by decide
  rcases family_descends (prefixWord ++ tailWord_835470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835474 : List Nat := [3, 2, 3, 2, 1, 1, 8]
def baseStart_835474 : Nat := 118140960795 + 835474 * 2 ^ 59
def prefixEnd_835474 : Nat := 4983230072969 + 3 ^ 40 * 835474 * 2
def baseEnd_835474 : Nat := 42370344329340191390887

theorem tailTrace_835474 : CollatzResearch.WordTrace tailWord_835474 prefixEnd_835474 42370344329340191390887 := by
  unfold tailWord_835474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618060043806965111092369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20314826783485240296246317 7618060043806965111092369)
  ·
    refine ⟨5713545032855223833319277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7618060043806965111092369 5713545032855223833319277)
    ·
      refine ⟨2142579387320708937494729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5713545032855223833319277 2142579387320708937494729)
      ·
        refine ⟨1606934540490531703121047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142579387320708937494729 1606934540490531703121047)
        ·
          refine ⟨2410401810735797554681571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606934540490531703121047 2410401810735797554681571)
          ·
            refine ⟨3615602716103696332022357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410401810735797554681571 3615602716103696332022357)
            ·
              refine ⟨42370344329340191390887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3615602716103696332022357 42370344329340191390887)
              ·
                rfl

theorem cell20_835474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_835474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835474 prefixEnd_835474 := by exact prefixLift 835474
  have htrace : WordTrace (prefixWord ++ tailWord_835474) baseStart_835474 baseEnd_835474 := by
    simpa [prefixWord, tailWord_835474, baseEnd_835474] using wordTrace_append hprefix tailTrace_835474
  have hstable : (prefixWord ++ tailWord_835474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835474).length < 2 ^ (prefixWord ++ tailWord_835474).sum := by decide
  have hdescent : baseEnd_835474 < baseStart_835474 := by decide
  rcases family_descends (prefixWord ++ tailWord_835474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835480 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 2]
def baseStart_835480 : Nat := 118140960795 + 835480 * 2 ^ 59
def prefixEnd_835480 : Nat := 4983230072969 + 3 ^ 40 * 835480 * 2
def baseEnd_835480 : Nat := 381335837527552368317959

theorem tailTrace_835480 : CollatzResearch.WordTrace tailWord_835480 prefixEnd_835480 381335837527552368317959 := by
  unfold tailWord_835480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15236229506603061734543947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20314972675470748979391929 15236229506603061734543947)
  ·
    refine ⟨22854344259904592601815921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15236229506603061734543947 22854344259904592601815921)
    ·
      refine ⟨17140758194928444451361941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22854344259904592601815921 17140758194928444451361941)
      ·
        refine ⟨803473040387270833657591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17140758194928444451361941 803473040387270833657591)
        ·
          refine ⟨1205209560580906250486387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803473040387270833657591 1205209560580906250486387)
          ·
            refine ⟨1807814340871359375729581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205209560580906250486387 1807814340871359375729581)
            ·
              refine ⟨677930377826759765898593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1807814340871359375729581 677930377826759765898593)
              ·
                refine ⟨508447783370069824423945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677930377826759765898593 508447783370069824423945)
                ·
                  refine ⟨381335837527552368317959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508447783370069824423945 381335837527552368317959)
                  ·
                    rfl

theorem cell20_835480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_835480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835480 prefixEnd_835480 := by exact prefixLift 835480
  have htrace : WordTrace (prefixWord ++ tailWord_835480) baseStart_835480 baseEnd_835480 := by
    simpa [prefixWord, tailWord_835480, baseEnd_835480] using wordTrace_append hprefix tailTrace_835480
  have hstable : (prefixWord ++ tailWord_835480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835480).length < 2 ^ (prefixWord ++ tailWord_835480).sum := by decide
  have hdescent : baseEnd_835480 < baseStart_835480 := by decide
  rcases family_descends (prefixWord ++ tailWord_835480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835484 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_835484 : Nat := 118140960795 + 835484 * 2 ^ 59
def prefixEnd_835484 : Nat := 4983230072969 + 3 ^ 40 * 835484 * 2
def baseEnd_835484 : Nat := 381337663236546132184609

theorem tailTrace_835484 : CollatzResearch.WordTrace tailWord_835484 prefixEnd_835484 381337663236546132184609 := by
  unfold tailWord_835484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15236302452595816076116753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20315069936794421434822337 15236302452595816076116753)
  ·
    refine ⟨11427226839446862057087565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15236302452595816076116753 11427226839446862057087565)
    ·
      refine ⟨4285210064792573271407837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11427226839446862057087565 4285210064792573271407837)
      ·
        refine ⟨1606953774297214976777939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4285210064792573271407837 1606953774297214976777939)
        ·
          refine ⟨2410430661445822465166909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606953774297214976777939 2410430661445822465166909)
          ·
            refine ⟨903911498042183424437591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2410430661445822465166909 903911498042183424437591)
            ·
              refine ⟨1355867247063275136656387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903911498042183424437591 1355867247063275136656387)
              ·
                refine ⟨2033800870594912704984581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355867247063275136656387 2033800870594912704984581)
                ·
                  refine ⟨381337663236546132184609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033800870594912704984581 381337663236546132184609)
                  ·
                    rfl

theorem cell20_835484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_835484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835484 prefixEnd_835484 := by exact prefixLift 835484
  have htrace : WordTrace (prefixWord ++ tailWord_835484) baseStart_835484 baseEnd_835484 := by
    simpa [prefixWord, tailWord_835484, baseEnd_835484] using wordTrace_append hprefix tailTrace_835484
  have hstable : (prefixWord ++ tailWord_835484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835484).length < 2 ^ (prefixWord ++ tailWord_835484).sum := by decide
  have hdescent : baseEnd_835484 < baseStart_835484 := by decide
  rcases family_descends (prefixWord ++ tailWord_835484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835543 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 2]
def baseStart_835543 : Nat := 118140960795 + 835543 * 2 ^ 59
def prefixEnd_835543 : Nat := 4983230072969 + 3 ^ 40 * 835543 * 2
def baseEnd_835543 : Nat := 381364592444204149217701

theorem tailTrace_835543 : CollatzResearch.WordTrace tailWord_835543 prefixEnd_835543 381364592444204149217701 := by
  unfold tailWord_835543
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474756811977885228631283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20316504541318590152420855 30474756811977885228631283)
  ·
    refine ⟨45712135217966827842946925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30474756811977885228631283 45712135217966827842946925)
    ·
      refine ⟨17142050706737560441105097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45712135217966827842946925 17142050706737560441105097)
      ·
        refine ⟨12856538030053170330828823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17142050706737560441105097 12856538030053170330828823)
        ·
          refine ⟨19284807045079755496243235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12856538030053170330828823 19284807045079755496243235)
          ·
            refine ⟨28927210567619633244364853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284807045079755496243235 28927210567619633244364853)
            ·
              refine ⟨2711925990714340616659205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28927210567619633244364853 2711925990714340616659205)
              ·
                refine ⟨508486123258938865623601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2711925990714340616659205 508486123258938865623601)
                ·
                  refine ⟨381364592444204149217701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508486123258938865623601 381364592444204149217701)
                  ·
                    rfl

theorem cell20_835543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 2].length) (baseStart_835543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835543 prefixEnd_835543 := by exact prefixLift 835543
  have htrace : WordTrace (prefixWord ++ tailWord_835543) baseStart_835543 baseEnd_835543 := by
    simpa [prefixWord, tailWord_835543, baseEnd_835543] using wordTrace_append hprefix tailTrace_835543
  have hstable : (prefixWord ++ tailWord_835543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835543).length < 2 ^ (prefixWord ++ tailWord_835543).sum := by decide
  have hdescent : baseEnd_835543 < baseStart_835543 := by decide
  rcases family_descends (prefixWord ++ tailWord_835543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835581 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 2]
def baseStart_835581 : Nat := 118140960795 + 835581 * 2 ^ 59
def prefixEnd_835581 : Nat := 4983230072969 + 3 ^ 40 * 835581 * 2
def baseEnd_835581 : Nat := 381381936679644905950879

theorem tailTrace_835581 : CollatzResearch.WordTrace tailWord_835581 prefixEnd_835581 381381936679644905950879 := by
  unfold tailWord_835581
  simp only [CollatzResearch.WordTrace]
  refine ⟨30476142785840217718514597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20317428523893478479009731 30476142785840217718514597)
  ·
    refine ⟨5714276772345040822221487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30476142785840217718514597 5714276772345040822221487)
    ·
      refine ⟨8571415158517561233332231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5714276772345040822221487 8571415158517561233332231)
      ·
        refine ⟨12857122737776341849998347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8571415158517561233332231 12857122737776341849998347)
        ·
          refine ⟨19285684106664512774997521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12857122737776341849998347 19285684106664512774997521)
          ·
            refine ⟨14464263079998384581248141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19285684106664512774997521 14464263079998384581248141)
            ·
              refine ⟨5424098654999394217968053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14464263079998384581248141 5424098654999394217968053)
              ·
                refine ⟨508509248906193207934505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5424098654999394217968053 508509248906193207934505)
                ·
                  refine ⟨381381936679644905950879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508509248906193207934505 381381936679644905950879)
                  ·
                    rfl

theorem cell20_835581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_835581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835581 prefixEnd_835581 := by exact prefixLift 835581
  have htrace : WordTrace (prefixWord ++ tailWord_835581) baseStart_835581 baseEnd_835581 := by
    simpa [prefixWord, tailWord_835581, baseEnd_835581] using wordTrace_append hprefix tailTrace_835581
  have hstable : (prefixWord ++ tailWord_835581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835581).length < 2 ^ (prefixWord ++ tailWord_835581).sum := by decide
  have hdescent : baseEnd_835581 < baseStart_835581 := by decide
  rcases family_descends (prefixWord ++ tailWord_835581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835626 : List Nat := [3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_835626 : Nat := 118140960795 + 835626 * 2 ^ 59
def prefixEnd_835626 : Nat := 4983230072969 + 3 ^ 40 * 835626 * 2
def baseEnd_835626 : Nat := 127134158635274916483565

theorem tailTrace_835626 : CollatzResearch.WordTrace tailWord_835626 prefixEnd_835626 127134158635274916483565 := by
  unfold tailWord_835626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619446017669297600975683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20318522713784793602601821 7619446017669297600975683)
  ·
    refine ⟨11429169026503946401463525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619446017669297600975683 11429169026503946401463525)
    ·
      refine ⟨2142969192469489950274411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11429169026503946401463525 2142969192469489950274411)
      ·
        refine ⟨3214453788704234925411617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142969192469489950274411 3214453788704234925411617)
        ·
          refine ⟨2410840341528176194058713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214453788704234925411617 2410840341528176194058713)
          ·
            refine ⟨1808130256146132145544035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410840341528176194058713 1808130256146132145544035)
            ·
              refine ⟨2712195384219198218316053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808130256146132145544035 2712195384219198218316053)
              ·
                refine ⟨127134158635274916483565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2712195384219198218316053 127134158635274916483565)
                ·
                  rfl

theorem cell20_835626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_835626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835626 prefixEnd_835626 := by exact prefixLift 835626
  have htrace : WordTrace (prefixWord ++ tailWord_835626) baseStart_835626 baseEnd_835626 := by
    simpa [prefixWord, tailWord_835626, baseEnd_835626] using wordTrace_append hprefix tailTrace_835626
  have hstable : (prefixWord ++ tailWord_835626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835626).length < 2 ^ (prefixWord ++ tailWord_835626).sum := by decide
  have hdescent : baseEnd_835626 < baseStart_835626 := by decide
  rcases family_descends (prefixWord ++ tailWord_835626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835685 : List Nat := [1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_835685 : Nat := 118140960795 + 835685 * 2 ^ 59
def prefixEnd_835685 : Nat := 4983230072969 + 3 ^ 40 * 835685 * 2
def baseEnd_835685 : Nat := 127143135037827588827929

theorem tailTrace_835685 : CollatzResearch.WordTrace tailWord_835685 prefixEnd_835685 127143135037827588827929 := by
  unfold tailWord_835685
  simp only [CollatzResearch.WordTrace]
  refine ⟨30479935977463443480300509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20319957318308962320200339 30479935977463443480300509)
  ·
    refine ⟨11429975991548791305112691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30479935977463443480300509 11429975991548791305112691)
    ·
      refine ⟨17144963987323186957669037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429975991548791305112691 17144963987323186957669037)
      ·
        refine ⟨6429361495246195109125889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17144963987323186957669037 6429361495246195109125889)
        ·
          refine ⟨4822021121434646331844417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6429361495246195109125889 4822021121434646331844417)
          ·
            refine ⟨3616515841075984748883313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4822021121434646331844417 3616515841075984748883313)
            ·
              refine ⟨2712386880806988561662485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616515841075984748883313 2712386880806988561662485)
              ·
                refine ⟨127143135037827588827929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2712386880806988561662485 127143135037827588827929)
                ·
                  rfl

theorem cell20_835685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_835685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835685 prefixEnd_835685 := by exact prefixLift 835685
  have htrace : WordTrace (prefixWord ++ tailWord_835685) baseStart_835685 baseEnd_835685 := by
    simpa [prefixWord, tailWord_835685, baseEnd_835685] using wordTrace_append hprefix tailTrace_835685
  have hstable : (prefixWord ++ tailWord_835685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835685).length < 2 ^ (prefixWord ++ tailWord_835685).sum := by decide
  have hdescent : baseEnd_835685 < baseStart_835685 := by decide
  rcases family_descends (prefixWord ++ tailWord_835685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835709 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_835709 : Nat := 118140960795 + 835709 * 2 ^ 59
def prefixEnd_835709 : Nat := 4983230072969 + 3 ^ 40 * 835709 * 2
def baseEnd_835709 : Nat := 381440359367445349683689

theorem tailTrace_835709 : CollatzResearch.WordTrace tailWord_835709 prefixEnd_835709 381440359367445349683689 := by
  unfold tailWord_835709
  simp only [CollatzResearch.WordTrace]
  refine ⟨30480811329376495579174181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20320540886250997052782787 30480811329376495579174181)
  ·
    refine ⟨5715152124258092921095159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30480811329376495579174181 5715152124258092921095159)
    ·
      refine ⟨8572728186387139381642739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5715152124258092921095159 8572728186387139381642739)
      ·
        refine ⟨12859092279580709072464109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572728186387139381642739 12859092279580709072464109)
        ·
          refine ⟨4822159604842765902174041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12859092279580709072464109 4822159604842765902174041)
          ·
            refine ⟨3616619703632074426630531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4822159604842765902174041 3616619703632074426630531)
            ·
              refine ⟨5424929555448111639945797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616619703632074426630531 5424929555448111639945797)
              ·
                refine ⟨1017174291646520932489837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5424929555448111639945797 1017174291646520932489837)
                ·
                  refine ⟨381440359367445349683689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017174291646520932489837 381440359367445349683689)
                  ·
                    rfl

theorem cell20_835709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_835709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835709 prefixEnd_835709 := by exact prefixLift 835709
  have htrace : WordTrace (prefixWord ++ tailWord_835709) baseStart_835709 baseEnd_835709 := by
    simpa [prefixWord, tailWord_835709, baseEnd_835709] using wordTrace_append hprefix tailTrace_835709
  have hstable : (prefixWord ++ tailWord_835709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835709).length < 2 ^ (prefixWord ++ tailWord_835709).sum := by decide
  have hdescent : baseEnd_835709 < baseStart_835709 := by decide
  rcases family_descends (prefixWord ++ tailWord_835709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835716 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_835716 : Nat := 118140960795 + 835716 * 2 ^ 59
def prefixEnd_835716 : Nat := 4983230072969 + 3 ^ 40 * 835716 * 2
def baseEnd_835716 : Nat := 381443554358184436450327

theorem tailTrace_835716 : CollatzResearch.WordTrace tailWord_835716 prefixEnd_835716 381443554358184436450327 := by
  unfold tailWord_835716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240533320175567887339501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20320711093567423849786001 15240533320175567887339501)
  ·
    refine ⟨5715199995065837957752313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15240533320175567887339501 5715199995065837957752313)
    ·
      refine ⟨4286399996299378468314235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5715199995065837957752313 4286399996299378468314235)
      ·
        refine ⟨6429599994449067702471353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286399996299378468314235 6429599994449067702471353)
        ·
          refine ⟨4822199995836800776853515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6429599994449067702471353 4822199995836800776853515)
          ·
            refine ⟨7233299993755201165280273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822199995836800776853515 7233299993755201165280273)
            ·
              refine ⟨5424974995316400873960205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7233299993755201165280273 5424974995316400873960205)
              ·
                refine ⟨2034365623243650327735077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5424974995316400873960205 2034365623243650327735077)
                ·
                  refine ⟨381443554358184436450327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034365623243650327735077 381443554358184436450327)
                  ·
                    rfl

theorem cell20_835716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_835716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835716 prefixEnd_835716 := by exact prefixLift 835716
  have htrace : WordTrace (prefixWord ++ tailWord_835716) baseStart_835716 baseEnd_835716 := by
    simpa [prefixWord, tailWord_835716, baseEnd_835716] using wordTrace_append hprefix tailTrace_835716
  have hstable : (prefixWord ++ tailWord_835716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835716).length < 2 ^ (prefixWord ++ tailWord_835716).sum := by decide
  have hdescent : baseEnd_835716 < baseStart_835716 := by decide
  rcases family_descends (prefixWord ++ tailWord_835716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835740 : List Nat := [2, 2, 3, 2, 1, 1, 5, 4]
def baseStart_835740 : Nat := 118140960795 + 835740 * 2 ^ 59
def prefixEnd_835740 : Nat := 4983230072969 + 3 ^ 40 * 835740 * 2
def baseEnd_835740 : Nat := 127151502870715673216743

theorem tailTrace_835740 : CollatzResearch.WordTrace tailWord_835740 prefixEnd_835740 127151502870715673216743 := by
  unfold tailWord_835740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240970996132093936776337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20321294661509458582368449 15240970996132093936776337)
  ·
    refine ⟨11430728247099070452582253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15240970996132093936776337 11430728247099070452582253)
    ·
      refine ⟨4286523092662151419718345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11430728247099070452582253 4286523092662151419718345)
      ·
        refine ⟨3214892319496613564788759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4286523092662151419718345 3214892319496613564788759)
        ·
          refine ⟨4822338479244920347183139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214892319496613564788759 4822338479244920347183139)
          ·
            refine ⟨7233507718867380520774709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822338479244920347183139 7233507718867380520774709)
            ·
              refine ⟨678141348643816923822629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7233507718867380520774709 678141348643816923822629)
              ·
                refine ⟨127151502870715673216743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678141348643816923822629 127151502870715673216743)
                ·
                  rfl

theorem cell20_835740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_835740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835740 prefixEnd_835740 := by exact prefixLift 835740
  have htrace : WordTrace (prefixWord ++ tailWord_835740) baseStart_835740 baseEnd_835740 := by
    simpa [prefixWord, tailWord_835740, baseEnd_835740] using wordTrace_append hprefix tailTrace_835740
  have hstable : (prefixWord ++ tailWord_835740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835740).length < 2 ^ (prefixWord ++ tailWord_835740).sum := by decide
  have hdescent : baseEnd_835740 < baseStart_835740 := by decide
  rcases family_descends (prefixWord ++ tailWord_835740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835768 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_835768 : Nat := 118140960795 + 835768 * 2 ^ 59
def prefixEnd_835768 : Nat := 4983230072969 + 3 ^ 40 * 835768 * 2
def baseEnd_835768 : Nat := 381467288575103366716781

theorem tailTrace_835768 : CollatzResearch.WordTrace tailWord_835768 prefixEnd_835768 381467288575103366716781 := by
  unfold tailWord_835768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15241481618081374327785979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20321975490775165770381305 15241481618081374327785979)
  ·
    refine ⟨22862222427122061491678969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15241481618081374327785979 22862222427122061491678969)
    ·
      refine ⟨17146666820341546118759227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22862222427122061491678969 17146666820341546118759227)
      ·
        refine ⟨25720000230512319178138841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17146666820341546118759227 25720000230512319178138841)
        ·
          refine ⟨19290000172884239383604131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25720000230512319178138841 19290000172884239383604131)
          ·
            refine ⟨28935000259326359075406197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19290000172884239383604131 28935000259326359075406197)
            ·
              refine ⟨2712656274311846163319331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28935000259326359075406197 2712656274311846163319331)
              ·
                refine ⟨4068984411467769244978997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712656274311846163319331 4068984411467769244978997)
                ·
                  refine ⟨381467288575103366716781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4068984411467769244978997 381467288575103366716781)
                  ·
                    rfl

theorem cell20_835768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_835768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835768 prefixEnd_835768 := by exact prefixLift 835768
  have htrace : WordTrace (prefixWord ++ tailWord_835768) baseStart_835768 baseEnd_835768 := by
    simpa [prefixWord, tailWord_835768, baseEnd_835768] using wordTrace_append hprefix tailTrace_835768
  have hstable : (prefixWord ++ tailWord_835768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835768).length < 2 ^ (prefixWord ++ tailWord_835768).sum := by decide
  have hdescent : baseEnd_835768 < baseStart_835768 := by decide
  rcases family_descends (prefixWord ++ tailWord_835768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835805 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 2]
def baseStart_835805 : Nat := 118140960795 + 835805 * 2 ^ 59
def prefixEnd_835805 : Nat := 4983230072969 + 3 ^ 40 * 835805 * 2
def baseEnd_835805 : Nat := 381484176383295682483297

theorem tailTrace_835805 : CollatzResearch.WordTrace tailWord_835805 prefixEnd_835805 381484176383295682483297 := by
  unfold tailWord_835805
  simp only [CollatzResearch.WordTrace]
  refine ⟨30484312737028703974668869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20322875158019135983112579 30484312737028703974668869)
  ·
    refine ⟨5715808638192881995250413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30484312737028703974668869 5715808638192881995250413)
    ·
      refine ⟨2143428239322330748218905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5715808638192881995250413 2143428239322330748218905)
      ·
        refine ⟨1607571179491748061164179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2143428239322330748218905 1607571179491748061164179)
        ·
          refine ⟨2411356769237622091746269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607571179491748061164179 2411356769237622091746269)
          ·
            refine ⟨904258788464108284404851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2411356769237622091746269 904258788464108284404851)
            ·
              refine ⟨1356388182696162426607277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904258788464108284404851 1356388182696162426607277)
              ·
                refine ⟨508645568511060909977729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1356388182696162426607277 508645568511060909977729)
                ·
                  refine ⟨381484176383295682483297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508645568511060909977729 381484176383295682483297)
                  ·
                    rfl

theorem cell20_835805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_835805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835805 prefixEnd_835805 := by exact prefixLift 835805
  have htrace : WordTrace (prefixWord ++ tailWord_835805) baseStart_835805 baseEnd_835805 := by
    simpa [prefixWord, tailWord_835805, baseEnd_835805] using wordTrace_append hprefix tailTrace_835805
  have hstable : (prefixWord ++ tailWord_835805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835805).length < 2 ^ (prefixWord ++ tailWord_835805).sum := by decide
  have hdescent : baseEnd_835805 < baseStart_835805 := by decide
  rcases family_descends (prefixWord ++ tailWord_835805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835851 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_835851 : Nat := 118140960795 + 835851 * 2 ^ 59
def prefixEnd_835851 : Nat := 4983230072969 + 3 ^ 40 * 835851 * 2
def baseEnd_835851 : Nat := 381505172036723966949775

theorem tailTrace_835851 : CollatzResearch.WordTrace tailWord_835851 prefixEnd_835851 381505172036723966949775 := by
  unfold tailWord_835851
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485990494862053830843407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20323993663241369220562271 30485990494862053830843407)
  ·
    refine ⟨45728985742293080746265111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30485990494862053830843407 45728985742293080746265111)
    ·
      refine ⟨68593478613439621119397667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45728985742293080746265111 68593478613439621119397667)
      ·
        refine ⟨102890217920159431679096501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68593478613439621119397667 102890217920159431679096501)
        ·
          refine ⟨9645957930014946719915297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102890217920159431679096501 9645957930014946719915297)
          ·
            refine ⟨7234468447511210039936473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9645957930014946719915297 7234468447511210039936473)
            ·
              refine ⟨5425851335633407529952355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234468447511210039936473 5425851335633407529952355)
              ·
                refine ⟨8138777003450111294928533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425851335633407529952355 8138777003450111294928533)
                ·
                  refine ⟨381505172036723966949775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8138777003450111294928533 381505172036723966949775)
                  ·
                    rfl

theorem cell20_835851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_835851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835851 prefixEnd_835851 := by exact prefixLift 835851
  have htrace : WordTrace (prefixWord ++ tailWord_835851) baseStart_835851 baseEnd_835851 := by
    simpa [prefixWord, tailWord_835851, baseEnd_835851] using wordTrace_append hprefix tailTrace_835851
  have hstable : (prefixWord ++ tailWord_835851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835851).length < 2 ^ (prefixWord ++ tailWord_835851).sum := by decide
  have hdescent : baseEnd_835851 < baseStart_835851 := by decide
  rcases family_descends (prefixWord ++ tailWord_835851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835892 : List Nat := [2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_835892 : Nat := 118140960795 + 835892 * 2 ^ 59
def prefixEnd_835892 : Nat := 4983230072969 + 3 ^ 40 * 835892 * 2
def baseEnd_835892 : Nat := 127174628517970015527647

theorem tailTrace_835892 : CollatzResearch.WordTrace tailWord_835892 prefixEnd_835892 127174628517970015527647 := by
  unfold tailWord_835892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15243742943856758916542965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20324990591809011888723953 15243742943856758916542965)
  ·
    refine ⟨1429100900986571148425903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15243742943856758916542965 1429100900986571148425903)
    ·
      refine ⟨2143651351479856722638855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429100900986571148425903 2143651351479856722638855)
      ·
        refine ⟨3215477027219785083958283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143651351479856722638855 3215477027219785083958283)
        ·
          refine ⟨4823215540829677625937425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215477027219785083958283 4823215540829677625937425)
          ·
            refine ⟨3617411655622258219453069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4823215540829677625937425 3617411655622258219453069)
            ·
              refine ⟨1356529370858346832294901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3617411655622258219453069 1356529370858346832294901)
              ·
                refine ⟨127174628517970015527647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1356529370858346832294901 127174628517970015527647)
                ·
                  rfl

theorem cell20_835892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_835892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835892 prefixEnd_835892 := by exact prefixLift 835892
  have htrace : WordTrace (prefixWord ++ tailWord_835892) baseStart_835892 baseEnd_835892 := by
    simpa [prefixWord, tailWord_835892, baseEnd_835892] using wordTrace_append hprefix tailTrace_835892
  have hstable : (prefixWord ++ tailWord_835892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835892).length < 2 ^ (prefixWord ++ tailWord_835892).sum := by decide
  have hdescent : baseEnd_835892 < baseStart_835892 := by decide
  rcases family_descends (prefixWord ++ tailWord_835892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835927 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_835927 : Nat := 118140960795 + 835927 * 2 ^ 59
def prefixEnd_835927 : Nat := 4983230072969 + 3 ^ 40 * 835927 * 2
def baseEnd_835927 : Nat := 381539860507605480416131

theorem tailTrace_835927 : CollatzResearch.WordTrace tailWord_835927 prefixEnd_835927 381539860507605480416131 := by
  unfold tailWord_835927
  simp only [CollatzResearch.WordTrace]
  refine ⟨30488762442586718810610035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20325841628391145873740023 30488762442586718810610035)
  ·
    refine ⟨45733143663880078215915053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30488762442586718810610035 45733143663880078215915053)
    ·
      refine ⟨17149928873955029330968145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45733143663880078215915053 17149928873955029330968145)
      ·
        refine ⟨12862446655466271998226109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17149928873955029330968145 12862446655466271998226109)
        ·
          refine ⟨4823417495799851999334791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12862446655466271998226109 4823417495799851999334791)
          ·
            refine ⟨7235126243699777999002187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823417495799851999334791 7235126243699777999002187)
            ·
              refine ⟨10852689365549666998503281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235126243699777999002187 10852689365549666998503281)
              ·
                refine ⟨8139517024162250248877461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10852689365549666998503281 8139517024162250248877461)
                ·
                  refine ⟨381539860507605480416131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8139517024162250248877461 381539860507605480416131)
                  ·
                    rfl

theorem cell20_835927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_835927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835927 prefixEnd_835927 := by exact prefixLift 835927
  have htrace : WordTrace (prefixWord ++ tailWord_835927) baseStart_835927 baseEnd_835927 := by
    simpa [prefixWord, tailWord_835927, baseEnd_835927] using wordTrace_append hprefix tailTrace_835927
  have hstable : (prefixWord ++ tailWord_835927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835927).length < 2 ^ (prefixWord ++ tailWord_835927).sum := by decide
  have hdescent : baseEnd_835927 < baseStart_835927 := by decide
  rcases family_descends (prefixWord ++ tailWord_835927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835944 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_835944 : Nat := 118140960795 + 835944 * 2 ^ 59
def prefixEnd_835944 : Nat := 4983230072969 + 3 ^ 40 * 835944 * 2
def baseEnd_835944 : Nat := 381547619770828976849395

theorem tailTrace_835944 : CollatzResearch.WordTrace tailWord_835944 prefixEnd_835944 381547619770828976849395 := by
  unfold tailWord_835944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15244691241762565356989443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20326254989016753809319257 15244691241762565356989443)
  ·
    refine ⟨22867036862643848035484165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15244691241762565356989443 22867036862643848035484165)
    ·
      refine ⟨4287569411745721506653281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22867036862643848035484165 4287569411745721506653281)
      ·
        refine ⟨3215677058809291129989961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4287569411745721506653281 3215677058809291129989961)
        ·
          refine ⟨2411757794106968347492471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3215677058809291129989961 2411757794106968347492471)
          ·
            refine ⟨3617636691160452521238707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411757794106968347492471 3617636691160452521238707)
            ·
              refine ⟨5426455036740678781858061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617636691160452521238707 5426455036740678781858061)
              ·
                refine ⟨2034920638777754543196773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5426455036740678781858061 2034920638777754543196773)
                ·
                  refine ⟨381547619770828976849395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034920638777754543196773 381547619770828976849395)
                  ·
                    rfl

theorem cell20_835944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_835944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835944 prefixEnd_835944 := by exact prefixLift 835944
  have htrace : WordTrace (prefixWord ++ tailWord_835944) baseStart_835944 baseEnd_835944 := by
    simpa [prefixWord, tailWord_835944, baseEnd_835944] using wordTrace_append hprefix tailTrace_835944
  have hstable : (prefixWord ++ tailWord_835944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835944).length < 2 ^ (prefixWord ++ tailWord_835944).sum := by decide
  have hdescent : baseEnd_835944 < baseStart_835944 := by decide
  rcases family_descends (prefixWord ++ tailWord_835944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835954 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_835954 : Nat := 118140960795 + 835954 * 2 ^ 59
def prefixEnd_835954 : Nat := 4983230072969 + 3 ^ 40 * 835954 * 2
def baseEnd_835954 : Nat := 381552184043313386516021

theorem tailTrace_835954 : CollatzResearch.WordTrace tailWord_835954 prefixEnd_835954 381552184043313386516021 := by
  unfold tailWord_835954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7622436803372225605460729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20326498142325934947895277 7622436803372225605460729)
  ·
    refine ⟨5716827602529169204095547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7622436803372225605460729 5716827602529169204095547)
    ·
      refine ⟨8575241403793753806143321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716827602529169204095547 8575241403793753806143321)
      ·
        refine ⟨6431431052845315354607491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8575241403793753806143321 6431431052845315354607491)
        ·
          refine ⟨9647146579267973031911237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431431052845315354607491 9647146579267973031911237)
          ·
            refine ⟨1808839983612744943483357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9647146579267973031911237 1808839983612744943483357)
            ·
              refine ⟨678314993854779353806259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1808839983612744943483357 678314993854779353806259)
              ·
                refine ⟨1017472490782169030709389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678314993854779353806259 1017472490782169030709389)
                ·
                  refine ⟨381552184043313386516021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017472490782169030709389 381552184043313386516021)
                  ·
                    rfl

theorem cell20_835954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_835954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_835954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_835954 prefixEnd_835954 := by exact prefixLift 835954
  have htrace : WordTrace (prefixWord ++ tailWord_835954) baseStart_835954 baseEnd_835954 := by
    simpa [prefixWord, tailWord_835954, baseEnd_835954] using wordTrace_append hprefix tailTrace_835954
  have hstable : (prefixWord ++ tailWord_835954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835954).length < 2 ^ (prefixWord ++ tailWord_835954).sum := by decide
  have hdescent : baseEnd_835954 < baseStart_835954 := by decide
  rcases family_descends (prefixWord ++ tailWord_835954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836050 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_836050 : Nat := 118140960795 + 836050 * 2 ^ 59
def prefixEnd_836050 : Nat := 4983230072969 + 3 ^ 40 * 836050 * 2
def baseEnd_836050 : Nat := 381596001059163719315629

theorem tailTrace_836050 : CollatzResearch.WordTrace tailWord_836050 prefixEnd_836050 381596001059163719315629 := by
  unfold tailWord_836050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7623312155285277704334401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20328832414094073878225069 7623312155285277704334401)
  ·
    refine ⟨5717484116463958278250801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7623312155285277704334401 5717484116463958278250801)
    ·
      refine ⟨4288113087347968708688101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5717484116463958278250801 4288113087347968708688101)
      ·
        refine ⟨804021203877744132879019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4288113087347968708688101 804021203877744132879019)
        ·
          refine ⟨1206031805816616199318529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804021203877744132879019 1206031805816616199318529)
          ·
            refine ⟨904523854362462149488897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206031805816616199318529 904523854362462149488897)
            ·
              refine ⟨678392890771846612116673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904523854362462149488897 678392890771846612116673)
              ·
                refine ⟨508794668078884959087505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678392890771846612116673 508794668078884959087505)
                ·
                  refine ⟨381596001059163719315629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508794668078884959087505 381596001059163719315629)
                  ·
                    rfl

theorem cell20_836050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_836050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836050 prefixEnd_836050 := by exact prefixLift 836050
  have htrace : WordTrace (prefixWord ++ tailWord_836050) baseStart_836050 baseEnd_836050 := by
    simpa [prefixWord, tailWord_836050, baseEnd_836050] using wordTrace_append hprefix tailTrace_836050
  have hstable : (prefixWord ++ tailWord_836050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836050).length < 2 ^ (prefixWord ++ tailWord_836050).sum := by decide
  have hdescent : baseEnd_836050 < baseStart_836050 := by decide
  rcases family_descends (prefixWord ++ tailWord_836050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836054 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_836054 : Nat := 118140960795 + 836054 * 2 ^ 59
def prefixEnd_836054 : Nat := 4983230072969 + 3 ^ 40 * 836054 * 2
def baseEnd_836054 : Nat := 381597826768157483182279

theorem tailTrace_836054 : CollatzResearch.WordTrace tailWord_836054 prefixEnd_836054 381597826768157483182279 := by
  unfold tailWord_836054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905837157070413718780201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20328929675417746333655477 1905837157070413718780201)
  ·
    refine ⟨1429377867802810289085151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1905837157070413718780201 1429377867802810289085151)
    ·
      refine ⟨2144066801704215433627727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429377867802810289085151 2144066801704215433627727)
      ·
        refine ⟨3216100202556323150441591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144066801704215433627727 3216100202556323150441591)
        ·
          refine ⟨4824150303834484725662387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216100202556323150441591 4824150303834484725662387)
          ·
            refine ⟨7236225455751727088493581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824150303834484725662387 7236225455751727088493581)
            ·
              refine ⟨2713584545906897658185093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7236225455751727088493581 2713584545906897658185093)
              ·
                refine ⟨508797102357543310909705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2713584545906897658185093 508797102357543310909705)
                ·
                  refine ⟨381597826768157483182279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508797102357543310909705 381597826768157483182279)
                  ·
                    rfl

theorem cell20_836054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_836054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836054 prefixEnd_836054 := by exact prefixLift 836054
  have htrace : WordTrace (prefixWord ++ tailWord_836054) baseStart_836054 baseEnd_836054 := by
    simpa [prefixWord, tailWord_836054, baseEnd_836054] using wordTrace_append hprefix tailTrace_836054
  have hstable : (prefixWord ++ tailWord_836054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836054).length < 2 ^ (prefixWord ++ tailWord_836054).sum := by decide
  have hdescent : baseEnd_836054 < baseStart_836054 := by decide
  rcases family_descends (prefixWord ++ tailWord_836054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836102 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_836102 : Nat := 118140960795 + 836102 * 2 ^ 59
def prefixEnd_836102 : Nat := 4983230072969 + 3 ^ 40 * 836102 * 2
def baseEnd_836102 : Nat := 381619735276082649582083

theorem tailTrace_836102 : CollatzResearch.WordTrace tailWord_836102 prefixEnd_836102 381619735276082649582083 := by
  unfold tailWord_836102
  simp only [CollatzResearch.WordTrace]
  refine ⟨952973288029772615569705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20330096811301815798820373 952973288029772615569705)
  ·
    refine ⟨714729966022329461677279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 952973288029772615569705 714729966022329461677279)
    ·
      refine ⟨1072094949033494192515919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714729966022329461677279 1072094949033494192515919)
      ·
        refine ⟨1608142423550241288773879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072094949033494192515919 1608142423550241288773879)
        ·
          refine ⟨2412213635325361933160819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608142423550241288773879 2412213635325361933160819)
          ·
            refine ⟨3618320452988042899741229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412213635325361933160819 3618320452988042899741229)
            ·
              refine ⟨1356870169870516087402961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3618320452988042899741229 1356870169870516087402961)
              ·
                refine ⟨1017652627402887065552221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356870169870516087402961 1017652627402887065552221)
                ·
                  refine ⟨381619735276082649582083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017652627402887065552221 381619735276082649582083)
                  ·
                    rfl

theorem cell20_836102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_836102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836102 prefixEnd_836102 := by exact prefixLift 836102
  have htrace : WordTrace (prefixWord ++ tailWord_836102) baseStart_836102 baseEnd_836102 := by
    simpa [prefixWord, tailWord_836102, baseEnd_836102] using wordTrace_append hprefix tailTrace_836102
  have hstable : (prefixWord ++ tailWord_836102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836102).length < 2 ^ (prefixWord ++ tailWord_836102).sum := by decide
  have hdescent : baseEnd_836102 < baseStart_836102 := by decide
  rcases family_descends (prefixWord ++ tailWord_836102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836103 : List Nat := [1, 1, 4, 3, 3, 1, 7]
def baseStart_836103 : Nat := 118140960795 + 836103 * 2 ^ 59
def prefixEnd_836103 : Nat := 4983230072969 + 3 ^ 40 * 836103 * 2
def baseEnd_836103 : Nat := 42402243522592343394305

theorem tailTrace_836103 : CollatzResearch.WordTrace tailWord_836103 prefixEnd_836103 42402243522592343394305 := by
  unfold tailWord_836103
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495181689949100869016963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20330121126632733912677975 30495181689949100869016963)
  ·
    refine ⟨45742772534923651303525445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30495181689949100869016963 45742772534923651303525445)
    ·
      refine ⟨8576769850298184619411021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45742772534923651303525445 8576769850298184619411021)
      ·
        refine ⟨3216288693861819232279133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8576769850298184619411021 3216288693861819232279133)
        ·
          refine ⟨1206108260198182212104675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3216288693861819232279133 1206108260198182212104675)
          ·
            refine ⟨1809162390297273318157013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206108260198182212104675 1809162390297273318157013)
            ·
              refine ⟨42402243522592343394305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1809162390297273318157013 42402243522592343394305)
              ·
                rfl

theorem cell20_836103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_836103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836103 prefixEnd_836103 := by exact prefixLift 836103
  have htrace : WordTrace (prefixWord ++ tailWord_836103) baseStart_836103 baseEnd_836103 := by
    simpa [prefixWord, tailWord_836103, baseEnd_836103] using wordTrace_append hprefix tailTrace_836103
  have hstable : (prefixWord ++ tailWord_836103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836103).length < 2 ^ (prefixWord ++ tailWord_836103).sum := by decide
  have hdescent : baseEnd_836103 < baseStart_836103 := by decide
  rcases family_descends (prefixWord ++ tailWord_836103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836109 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 2]
def baseStart_836109 : Nat := 118140960795 + 836109 * 2 ^ 59
def prefixEnd_836109 : Nat := 4983230072969 + 3 ^ 40 * 836109 * 2
def baseEnd_836109 : Nat := 381622930266821736348721

theorem tailTrace_836109 : CollatzResearch.WordTrace tailWord_836109 prefixEnd_836109 381622930266821736348721 := by
  unfold tailWord_836109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495400527927363893735381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20330267018618242595823587 30495400527927363893735381)
  ·
    refine ⟨714735949873297591259423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30495400527927363893735381 714735949873297591259423)
    ·
      refine ⟨1072103924809946386889135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714735949873297591259423 1072103924809946386889135)
      ·
        refine ⟨1608155887214919580333703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072103924809946386889135 1608155887214919580333703)
        ·
          refine ⟨2412233830822379370500555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608155887214919580333703 2412233830822379370500555)
          ·
            refine ⟨3618350746233569055750833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412233830822379370500555 3618350746233569055750833)
            ·
              refine ⟨2713763059675176791813125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618350746233569055750833 2713763059675176791813125)
              ·
                refine ⟨508830573689095648464961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2713763059675176791813125 508830573689095648464961)
                ·
                  refine ⟨381622930266821736348721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508830573689095648464961 381622930266821736348721)
                  ·
                    rfl

theorem cell20_836109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_836109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836109 prefixEnd_836109 := by exact prefixLift 836109
  have htrace : WordTrace (prefixWord ++ tailWord_836109) baseStart_836109 baseEnd_836109 := by
    simpa [prefixWord, tailWord_836109, baseEnd_836109] using wordTrace_append hprefix tailTrace_836109
  have hstable : (prefixWord ++ tailWord_836109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836109).length < 2 ^ (prefixWord ++ tailWord_836109).sum := by decide
  have hdescent : baseEnd_836109 < baseStart_836109 := by decide
  rcases family_descends (prefixWord ++ tailWord_836109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836164 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 4]
def baseStart_836164 : Nat := 118140960795 + 836164 * 2 ^ 59
def prefixEnd_836164 : Nat := 4983230072969 + 3 ^ 40 * 836164 * 2
def baseEnd_836164 : Nat := 381648033765485989515163

theorem tailTrace_836164 : CollatzResearch.WordTrace tailWord_836164 prefixEnd_836164 381648033765485989515163 := by
  unfold tailWord_836164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15248703271364054143493773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20331604361818738857991697 15248703271364054143493773)
  ·
    refine ⟨5718263726761520303810165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15248703271364054143493773 5718263726761520303810165)
    ·
      refine ⟨536087224383892528482203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5718263726761520303810165 536087224383892528482203)
      ·
        refine ⟨804130836575838792723305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536087224383892528482203 804130836575838792723305)
        ·
          refine ⟨603098127431879094542479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804130836575838792723305 603098127431879094542479)
          ·
            refine ⟨904647191147818641813719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603098127431879094542479 904647191147818641813719)
            ·
              refine ⟨1356970786721727962720579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904647191147818641813719 1356970786721727962720579)
              ·
                refine ⟨2035456180082591944080869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356970786721727962720579 2035456180082591944080869)
                ·
                  refine ⟨381648033765485989515163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035456180082591944080869 381648033765485989515163)
                  ·
                    rfl

theorem cell20_836164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_836164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836164 prefixEnd_836164 := by exact prefixLift 836164
  have htrace : WordTrace (prefixWord ++ tailWord_836164) baseStart_836164 baseEnd_836164 := by
    simpa [prefixWord, tailWord_836164, baseEnd_836164] using wordTrace_append hprefix tailTrace_836164
  have hstable : (prefixWord ++ tailWord_836164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836164).length < 2 ^ (prefixWord ++ tailWord_836164).sum := by decide
  have hdescent : baseEnd_836164 < baseStart_836164 := by decide
  rcases family_descends (prefixWord ++ tailWord_836164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836207 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_836207 : Nat := 118140960795 + 836207 * 2 ^ 59
def prefixEnd_836207 : Nat := 4983230072969 + 3 ^ 40 * 836207 * 2
def baseEnd_836207 : Nat := 381667660137168951081653

theorem tailTrace_836207 : CollatzResearch.WordTrace tailWord_836207 prefixEnd_836207 381667660137168951081653 := by
  unfold tailWord_836207
  simp only [CollatzResearch.WordTrace]
  refine ⟨30498974881572326630802875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20332649921048217753868583 30498974881572326630802875)
  ·
    refine ⟨45748462322358489946204313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30498974881572326630802875 45748462322358489946204313)
    ·
      refine ⟨34311346741768867459653235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45748462322358489946204313 34311346741768867459653235)
      ·
        refine ⟨51467020112653301189479853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34311346741768867459653235 51467020112653301189479853)
        ·
          refine ⟨19300132542244987946054945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51467020112653301189479853 19300132542244987946054945)
          ·
            refine ⟨14475099406683740959541209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19300132542244987946054945 14475099406683740959541209)
            ·
              refine ⟨10856324555012805719655907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14475099406683740959541209 10856324555012805719655907)
              ·
                refine ⟨16284486832519208579483861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10856324555012805719655907 16284486832519208579483861)
                ·
                  refine ⟨381667660137168951081653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16284486832519208579483861 381667660137168951081653)
                  ·
                    rfl

theorem cell20_836207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_836207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836207 prefixEnd_836207 := by exact prefixLift 836207
  have htrace : WordTrace (prefixWord ++ tailWord_836207) baseStart_836207 baseEnd_836207 := by
    simpa [prefixWord, tailWord_836207, baseEnd_836207] using wordTrace_append hprefix tailTrace_836207
  have hstable : (prefixWord ++ tailWord_836207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836207).length < 2 ^ (prefixWord ++ tailWord_836207).sum := by decide
  have hdescent : baseEnd_836207 < baseStart_836207 := by decide
  rcases family_descends (prefixWord ++ tailWord_836207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836224 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_836224 : Nat := 118140960795 + 836224 * 2 ^ 59
def prefixEnd_836224 : Nat := 4983230072969 + 3 ^ 40 * 836224 * 2
def baseEnd_836224 : Nat := 381675419400392447514917

theorem tailTrace_836224 : CollatzResearch.WordTrace tailWord_836224 prefixEnd_836224 381675419400392447514917 := by
  unfold tailWord_836224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15249797461255369267085863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20333063281673825689447817 15249797461255369267085863)
  ·
    refine ⟨22874696191883053900628795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15249797461255369267085863 22874696191883053900628795)
    ·
      refine ⟨34312044287824580850943193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22874696191883053900628795 34312044287824580850943193)
      ·
        refine ⟨25734033215868435638207395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34312044287824580850943193 25734033215868435638207395)
        ·
          refine ⟨38601049823802653457311093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25734033215868435638207395 38601049823802653457311093)
          ·
            refine ⟨3618848420981498761622915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38601049823802653457311093 3618848420981498761622915)
            ·
              refine ⟨5428272631472248142434373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618848420981498761622915 5428272631472248142434373)
              ·
                refine ⟨1017801118401046526706445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5428272631472248142434373 1017801118401046526706445)
                ·
                  refine ⟨381675419400392447514917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017801118401046526706445 381675419400392447514917)
                  ·
                    rfl

theorem cell20_836224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_836224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836224 prefixEnd_836224 := by exact prefixLift 836224
  have htrace : WordTrace (prefixWord ++ tailWord_836224) baseStart_836224 baseEnd_836224 := by
    simpa [prefixWord, tailWord_836224, baseEnd_836224] using wordTrace_append hprefix tailTrace_836224
  have hstable : (prefixWord ++ tailWord_836224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836224).length < 2 ^ (prefixWord ++ tailWord_836224).sum := by decide
  have hdescent : baseEnd_836224 < baseStart_836224 := by decide
  rcases family_descends (prefixWord ++ tailWord_836224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836227 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 2]
def baseStart_836227 : Nat := 118140960795 + 836227 * 2 ^ 59
def prefixEnd_836227 : Nat := 4983230072969 + 3 ^ 40 * 836227 * 2
def baseEnd_836227 : Nat := 381676788682137770414905

theorem tailTrace_836227 : CollatzResearch.WordTrace tailWord_836227 prefixEnd_836227 381676788682137770414905 := by
  unfold tailWord_836227
  simp only [CollatzResearch.WordTrace]
  refine ⟨30499704341499870046530935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20333136227666580031020623 30499704341499870046530935)
  ·
    refine ⟨45749556512249805069796403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30499704341499870046530935 45749556512249805069796403)
    ·
      refine ⟨68624334768374707604694605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45749556512249805069796403 68624334768374707604694605)
      ·
        refine ⟨25734125538140515351760477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68624334768374707604694605 25734125538140515351760477)
        ·
          refine ⟨9650297076802693256910179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25734125538140515351760477 9650297076802693256910179)
          ·
            refine ⟨14475445615204039885365269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9650297076802693256910179 14475445615204039885365269)
            ·
              refine ⟨678536513212689369626497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14475445615204039885365269 678536513212689369626497)
              ·
                refine ⟨508902384909517027219873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678536513212689369626497 508902384909517027219873)
                ·
                  refine ⟨381676788682137770414905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508902384909517027219873 381676788682137770414905)
                  ·
                    rfl

theorem cell20_836227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 2].length) (baseStart_836227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836227 prefixEnd_836227 := by exact prefixLift 836227
  have htrace : WordTrace (prefixWord ++ tailWord_836227) baseStart_836227 baseEnd_836227 := by
    simpa [prefixWord, tailWord_836227, baseEnd_836227] using wordTrace_append hprefix tailTrace_836227
  have hstable : (prefixWord ++ tailWord_836227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836227).length < 2 ^ (prefixWord ++ tailWord_836227).sum := by decide
  have hdescent : baseEnd_836227 < baseStart_836227 := by decide
  rcases family_descends (prefixWord ++ tailWord_836227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836231 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_836231 : Nat := 118140960795 + 836231 * 2 ^ 59
def prefixEnd_836231 : Nat := 4983230072969 + 3 ^ 40 * 836231 * 2
def baseEnd_836231 : Nat := 381678614391131534281555

theorem tailTrace_836231 : CollatzResearch.WordTrace tailWord_836231 prefixEnd_836231 381678614391131534281555 := by
  unfold tailWord_836231
  simp only [CollatzResearch.WordTrace]
  refine ⟨30499850233485378729676547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20333233488990252486451031 30499850233485378729676547)
  ·
    refine ⟨45749775350228068094514821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30499850233485378729676547 45749775350228068094514821)
    ·
      refine ⟨8578082878167762767721529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45749775350228068094514821 8578082878167762767721529)
      ·
        refine ⟨6433562158625822075791147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8578082878167762767721529 6433562158625822075791147)
        ·
          refine ⟨9650343237938733113686721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6433562158625822075791147 9650343237938733113686721)
          ·
            refine ⟨7237757428454049835265041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9650343237938733113686721 7237757428454049835265041)
            ·
              refine ⟨5428318071340537376448781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7237757428454049835265041 5428318071340537376448781)
              ·
                refine ⟨2035619276752701516168293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5428318071340537376448781 2035619276752701516168293)
                ·
                  refine ⟨381678614391131534281555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035619276752701516168293 381678614391131534281555)
                  ·
                    rfl

theorem cell20_836231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_836231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836231 prefixEnd_836231 := by exact prefixLift 836231
  have htrace : WordTrace (prefixWord ++ tailWord_836231) baseStart_836231 baseEnd_836231 := by
    simpa [prefixWord, tailWord_836231, baseEnd_836231] using wordTrace_append hprefix tailTrace_836231
  have hstable : (prefixWord ++ tailWord_836231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836231).length < 2 ^ (prefixWord ++ tailWord_836231).sum := by decide
  have hdescent : baseEnd_836231 < baseStart_836231 := by decide
  rcases family_descends (prefixWord ++ tailWord_836231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836234 : List Nat := [3, 1, 2, 3, 3, 2, 1, 5]
def baseStart_836234 : Nat := 118140960795 + 836234 * 2 ^ 59
def prefixEnd_836234 : Nat := 4983230072969 + 3 ^ 40 * 836234 * 2
def baseEnd_836234 : Nat := 127226661224292285727181

theorem tailTrace_836234 : CollatzResearch.WordTrace tailWord_836234 prefixEnd_836234 127226661224292285727181 := by
  unfold tailWord_836234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624989913118627560508939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20333306434983006828023837 7624989913118627560508939)
  ·
    refine ⟨11437484869677941340763409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7624989913118627560508939 11437484869677941340763409)
    ·
      refine ⟨8578113652258456005572557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11437484869677941340763409 8578113652258456005572557)
      ·
        refine ⟨3216792619596921002089709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8578113652258456005572557 3216792619596921002089709)
        ·
          refine ⟨1206297232348845375783641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3216792619596921002089709 1206297232348845375783641)
          ·
            refine ⟨904722924261634031837731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206297232348845375783641 904722924261634031837731)
            ·
              refine ⟨1357084386392451047756597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904722924261634031837731 1357084386392451047756597)
              ·
                refine ⟨127226661224292285727181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1357084386392451047756597 127226661224292285727181)
                ·
                  rfl

theorem cell20_836234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_836234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836234 prefixEnd_836234 := by exact prefixLift 836234
  have htrace : WordTrace (prefixWord ++ tailWord_836234) baseStart_836234 baseEnd_836234 := by
    simpa [prefixWord, tailWord_836234, baseEnd_836234] using wordTrace_append hprefix tailTrace_836234
  have hstable : (prefixWord ++ tailWord_836234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836234).length < 2 ^ (prefixWord ++ tailWord_836234).sum := by decide
  have hdescent : baseEnd_836234 < baseStart_836234 := by decide
  rcases family_descends (prefixWord ++ tailWord_836234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836245 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_836245 : Nat := 118140960795 + 836245 * 2 ^ 59
def prefixEnd_836245 : Nat := 4983230072969 + 3 ^ 40 * 836245 * 2
def baseEnd_836245 : Nat := 381685004372609707814831

theorem tailTrace_836245 : CollatzResearch.WordTrace tailWord_836245 prefixEnd_836245 381685004372609707814831 := by
  unfold tailWord_836245
  simp only [CollatzResearch.WordTrace]
  refine ⟨30500360855434659120686189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20333573903623106080457459 30500360855434659120686189)
  ·
    refine ⟨11437635320787997170257321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30500360855434659120686189 11437635320787997170257321)
    ·
      refine ⟨8578226490590997877692991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11437635320787997170257321 8578226490590997877692991)
      ·
        refine ⟨12867339735886496816539487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8578226490590997877692991 12867339735886496816539487)
        ·
          refine ⟨19301009603829745224809231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12867339735886496816539487 19301009603829745224809231)
          ·
            refine ⟨28951514405744617837213847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19301009603829745224809231 28951514405744617837213847)
            ·
              refine ⟨43427271608616926755820771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28951514405744617837213847 43427271608616926755820771)
              ·
                refine ⟨65140907412925390133731157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43427271608616926755820771 65140907412925390133731157)
                ·
                  refine ⟨381685004372609707814831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65140907412925390133731157 381685004372609707814831)
                  ·
                    rfl

theorem cell20_836245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_836245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836245 prefixEnd_836245 := by exact prefixLift 836245
  have htrace : WordTrace (prefixWord ++ tailWord_836245) baseStart_836245 baseEnd_836245 := by
    simpa [prefixWord, tailWord_836245, baseEnd_836245] using wordTrace_append hprefix tailTrace_836245
  have hstable : (prefixWord ++ tailWord_836245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836245).length < 2 ^ (prefixWord ++ tailWord_836245).sum := by decide
  have hdescent : baseEnd_836245 < baseStart_836245 := by decide
  rcases family_descends (prefixWord ++ tailWord_836245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836286 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_836286 : Nat := 118140960795 + 836286 * 2 ^ 59
def prefixEnd_836286 : Nat := 4983230072969 + 3 ^ 40 * 836286 * 2
def baseEnd_836286 : Nat := 381703717889795787447997

theorem tailTrace_836286 : CollatzResearch.WordTrace tailWord_836286 prefixEnd_836286 381703717889795787447997 := by
  unfold tailWord_836286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812732031035765390366089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20334570832190748748619141 3812732031035765390366089)
  ·
    refine ⟨2859549023276824042774567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3812732031035765390366089 2859549023276824042774567)
    ·
      refine ⟨4289323534915236064161851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859549023276824042774567 4289323534915236064161851)
      ·
        refine ⟨6433985302372854096242777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289323534915236064161851 6433985302372854096242777)
        ·
          refine ⟨4825488976779640572182083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6433985302372854096242777 4825488976779640572182083)
          ·
            refine ⟨7238233465169460858273125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825488976779640572182083 7238233465169460858273125)
            ·
              refine ⟨1357168774719273910926211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7238233465169460858273125 1357168774719273910926211)
              ·
                refine ⟨2035753162078910866389317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357168774719273910926211 2035753162078910866389317)
                ·
                  refine ⟨381703717889795787447997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035753162078910866389317 381703717889795787447997)
                  ·
                    rfl

theorem cell20_836286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_836286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836286 prefixEnd_836286 := by exact prefixLift 836286
  have htrace : WordTrace (prefixWord ++ tailWord_836286) baseStart_836286 baseEnd_836286 := by
    simpa [prefixWord, tailWord_836286, baseEnd_836286] using wordTrace_append hprefix tailTrace_836286
  have hstable : (prefixWord ++ tailWord_836286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836286).length < 2 ^ (prefixWord ++ tailWord_836286).sum := by decide
  have hdescent : baseEnd_836286 < baseStart_836286 := by decide
  rcases family_descends (prefixWord ++ tailWord_836286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836314 : List Nat := [3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_836314 : Nat := 118140960795 + 836314 * 2 ^ 59
def prefixEnd_836314 : Nat := 4983230072969 + 3 ^ 40 * 836314 * 2
def baseEnd_836314 : Nat := 127238832617584044838183

theorem tailTrace_836314 : CollatzResearch.WordTrace tailWord_836314 prefixEnd_836314 127238832617584044838183 := by
  unfold tailWord_836314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625719373046170976236999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20335251661456455936631997 7625719373046170976236999)
  ·
    refine ⟨11438579059569256464355499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7625719373046170976236999 11438579059569256464355499)
    ·
      refine ⟨17157868589353884696533249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438579059569256464355499 17157868589353884696533249)
      ·
        refine ⟨12868401442015413522399937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17157868589353884696533249 12868401442015413522399937)
        ·
          refine ⟨9651301081511560141799953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12868401442015413522399937 9651301081511560141799953)
          ·
            refine ⟨7238475811133670106349965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651301081511560141799953 7238475811133670106349965)
            ·
              refine ⟨2714428429175126289881237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7238475811133670106349965 2714428429175126289881237)
              ·
                refine ⟨127238832617584044838183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2714428429175126289881237 127238832617584044838183)
                ·
                  rfl

theorem cell20_836314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_836314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836314 prefixEnd_836314 := by exact prefixLift 836314
  have htrace : WordTrace (prefixWord ++ tailWord_836314) baseStart_836314 baseEnd_836314 := by
    simpa [prefixWord, tailWord_836314, baseEnd_836314] using wordTrace_append hprefix tailTrace_836314
  have hstable : (prefixWord ++ tailWord_836314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836314).length < 2 ^ (prefixWord ++ tailWord_836314).sum := by decide
  have hdescent : baseEnd_836314 < baseStart_836314 := by decide
  rcases family_descends (prefixWord ++ tailWord_836314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836338 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_836338 : Nat := 118140960795 + 836338 * 2 ^ 59
def prefixEnd_836338 : Nat := 4983230072969 + 3 ^ 40 * 836338 * 2
def baseEnd_836338 : Nat := 381727452106714717714451

theorem tailTrace_836338 : CollatzResearch.WordTrace tailWord_836338 prefixEnd_836338 381727452106714717714451 := by
  unfold tailWord_836338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625938211024434000955417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20335835229398490669214445 7625938211024434000955417)
  ·
    refine ⟨5719453658268325500716563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7625938211024434000955417 5719453658268325500716563)
    ·
      refine ⟨8579180487402488251074845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719453658268325500716563 8579180487402488251074845)
      ·
        refine ⟨3217192682775933094153067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8579180487402488251074845 3217192682775933094153067)
        ·
          refine ⟨4825789024163899641229601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217192682775933094153067 4825789024163899641229601)
          ·
            refine ⟨3619341768122924730922201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4825789024163899641229601 3619341768122924730922201)
            ·
              refine ⟨2714506326092193548191651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619341768122924730922201 2714506326092193548191651)
              ·
                refine ⟨4071759489138290322287477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714506326092193548191651 4071759489138290322287477)
                ·
                  refine ⟨381727452106714717714451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071759489138290322287477 381727452106714717714451)
                  ·
                    rfl

theorem cell20_836338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_836338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836338 prefixEnd_836338 := by exact prefixLift 836338
  have htrace : WordTrace (prefixWord ++ tailWord_836338) baseStart_836338 baseEnd_836338 := by
    simpa [prefixWord, tailWord_836338, baseEnd_836338] using wordTrace_append hprefix tailTrace_836338
  have hstable : (prefixWord ++ tailWord_836338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836338).length < 2 ^ (prefixWord ++ tailWord_836338).sum := by decide
  have hdescent : baseEnd_836338 < baseStart_836338 := by decide
  rcases family_descends (prefixWord ++ tailWord_836338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836417 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 4]
def baseStart_836417 : Nat := 118140960795 + 836417 * 2 ^ 59
def prefixEnd_836417 : Nat := 4983230072969 + 3 ^ 40 * 836417 * 2
def baseEnd_836417 : Nat := 381763509859341554080795

theorem tailTrace_836417 : CollatzResearch.WordTrace tailWord_836417 prefixEnd_836417 381763509859341554080795 := by
  unfold tailWord_836417
  simp only [CollatzResearch.WordTrace]
  refine ⟨30506634210811532495947505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20337756140541021663965003 30506634210811532495947505)
  ·
    refine ⟨22879975658108649371960629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30506634210811532495947505 22879975658108649371960629)
    ·
      refine ⟨2144997717947685878621309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22879975658108649371960629 2144997717947685878621309)
      ·
        refine ⟨804374144230382204482991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2144997717947685878621309 804374144230382204482991)
        ·
          refine ⟨1206561216345573306724487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804374144230382204482991 1206561216345573306724487)
          ·
            refine ⟨1809841824518359960086731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206561216345573306724487 1809841824518359960086731)
            ·
              refine ⟨2714762736777539940130097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809841824518359960086731 2714762736777539940130097)
              ·
                refine ⟨2036072052583154955097573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714762736777539940130097 2036072052583154955097573)
                ·
                  refine ⟨381763509859341554080795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036072052583154955097573 381763509859341554080795)
                  ·
                    rfl

theorem cell20_836417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_836417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836417 prefixEnd_836417 := by exact prefixLift 836417
  have htrace : WordTrace (prefixWord ++ tailWord_836417) baseStart_836417 baseEnd_836417 := by
    simpa [prefixWord, tailWord_836417, baseEnd_836417] using wordTrace_append hprefix tailTrace_836417
  have hstable : (prefixWord ++ tailWord_836417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836417).length < 2 ^ (prefixWord ++ tailWord_836417).sum := by decide
  have hdescent : baseEnd_836417 < baseStart_836417 := by decide
  rcases family_descends (prefixWord ++ tailWord_836417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836452 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_836452 : Nat := 118140960795 + 836452 * 2 ^ 59
def prefixEnd_836452 : Nat := 4983230072969 + 3 ^ 40 * 836452 * 2
def baseEnd_836452 : Nat := 381779484813036987913985

theorem tailTrace_836452 : CollatzResearch.WordTrace tailWord_836452 prefixEnd_836452 381779484813036987913985 := by
  unfold tailWord_836452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15253955382842366736735805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20338607177123155648981073 15253955382842366736735805)
  ·
    refine ⟨5720233268565887526275927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15253955382842366736735805 5720233268565887526275927)
    ·
      refine ⟨8580349902848831289413891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5720233268565887526275927 8580349902848831289413891)
      ·
        refine ⟨12870524854273246934120837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8580349902848831289413891 12870524854273246934120837)
        ·
          refine ⟨2413223410176233800147657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12870524854273246934120837 2413223410176233800147657)
          ·
            refine ⟨1809917557632175350110743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413223410176233800147657 1809917557632175350110743)
            ·
              refine ⟨2714876336448263025166115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809917557632175350110743 2714876336448263025166115)
              ·
                refine ⟨4072314504672394537749173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714876336448263025166115 4072314504672394537749173)
                ·
                  refine ⟨381779484813036987913985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072314504672394537749173 381779484813036987913985)
                  ·
                    rfl

theorem cell20_836452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_836452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836452 prefixEnd_836452 := by exact prefixLift 836452
  have htrace : WordTrace (prefixWord ++ tailWord_836452) baseStart_836452 baseEnd_836452 := by
    simpa [prefixWord, tailWord_836452, baseEnd_836452] using wordTrace_append hprefix tailTrace_836452
  have hstable : (prefixWord ++ tailWord_836452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836452).length < 2 ^ (prefixWord ++ tailWord_836452).sum := by decide
  have hdescent : baseEnd_836452 < baseStart_836452 := by decide
  rcases family_descends (prefixWord ++ tailWord_836452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836480 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_836480 : Nat := 118140960795 + 836480 * 2 ^ 59
def prefixEnd_836480 : Nat := 4983230072969 + 3 ^ 40 * 836480 * 2
def baseEnd_836480 : Nat := 381792264775993334980537

theorem tailTrace_836480 : CollatzResearch.WordTrace tailWord_836480 prefixEnd_836480 381792264775993334980537 := by
  unfold tailWord_836480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254466004791647127745447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20339288006388862836993929 15254466004791647127745447)
  ·
    refine ⟨22881699007187470691618171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15254466004791647127745447 22881699007187470691618171)
    ·
      refine ⟨34322548510781206037427257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22881699007187470691618171 34322548510781206037427257)
      ·
        refine ⟨25741911383085904528070443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34322548510781206037427257 25741911383085904528070443)
        ·
          refine ⟨38612867074628856792105665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25741911383085904528070443 38612867074628856792105665)
          ·
            refine ⟨28959650305971642594079249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38612867074628856792105665 28959650305971642594079249)
            ·
              refine ⟨21719737729478731945559437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28959650305971642594079249 21719737729478731945559437)
              ·
                refine ⟨8144901648554524479584789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21719737729478731945559437 8144901648554524479584789)
                ·
                  refine ⟨381792264775993334980537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8144901648554524479584789 381792264775993334980537)
                  ·
                    rfl

theorem cell20_836480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_836480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836480 prefixEnd_836480 := by exact prefixLift 836480
  have htrace : WordTrace (prefixWord ++ tailWord_836480) baseStart_836480 baseEnd_836480 := by
    simpa [prefixWord, tailWord_836480, baseEnd_836480] using wordTrace_append hprefix tailTrace_836480
  have hstable : (prefixWord ++ tailWord_836480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836480).length < 2 ^ (prefixWord ++ tailWord_836480).sum := by decide
  have hdescent : baseEnd_836480 < baseStart_836480 := by decide
  rcases family_descends (prefixWord ++ tailWord_836480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836490 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_836490 : Nat := 118140960795 + 836490 * 2 ^ 59
def prefixEnd_836490 : Nat := 4983230072969 + 3 ^ 40 * 836490 * 2
def baseEnd_836490 : Nat := 381796829048477744647163

theorem tailTrace_836490 : CollatzResearch.WordTrace tailWord_836490 prefixEnd_836490 381796829048477744647163 := by
  unfold tailWord_836490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627324184886766490838731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20339531159698043975569949 7627324184886766490838731)
  ·
    refine ⟨11440986277330149736258097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7627324184886766490838731 11440986277330149736258097)
    ·
      refine ⟨8580739707997612302193573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11440986277330149736258097 8580739707997612302193573)
      ·
        refine ⟨1608888695249552306661295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8580739707997612302193573 1608888695249552306661295)
        ·
          refine ⟨2413333042874328459991943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608888695249552306661295 2413333042874328459991943)
          ·
            refine ⟨3619999564311492689987915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413333042874328459991943 3619999564311492689987915)
            ·
              refine ⟨5429999346467239034981873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619999564311492689987915 5429999346467239034981873)
              ·
                refine ⟨4072499509850429276236405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429999346467239034981873 4072499509850429276236405)
                ·
                  refine ⟨381796829048477744647163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072499509850429276236405 381796829048477744647163)
                  ·
                    rfl

theorem cell20_836490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_836490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836490 prefixEnd_836490 := by exact prefixLift 836490
  have htrace : WordTrace (prefixWord ++ tailWord_836490) baseStart_836490 baseEnd_836490 := by
    simpa [prefixWord, tailWord_836490, baseEnd_836490] using wordTrace_append hprefix tailTrace_836490
  have hstable : (prefixWord ++ tailWord_836490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836490).length < 2 ^ (prefixWord ++ tailWord_836490).sum := by decide
  have hdescent : baseEnd_836490 < baseStart_836490 := by decide
  rcases family_descends (prefixWord ++ tailWord_836490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836514 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_836514 : Nat := 118140960795 + 836514 * 2 ^ 59
def prefixEnd_836514 : Nat := 4983230072969 + 3 ^ 40 * 836514 * 2
def baseEnd_836514 : Nat := 381807783302440327847065

theorem tailTrace_836514 : CollatzResearch.WordTrace tailWord_836514 prefixEnd_836514 381807783302440327847065 := by
  unfold tailWord_836514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627543022865029515557149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20340114727640078708152397 7627543022865029515557149)
  ·
    refine ⟨2860328633574386068333931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7627543022865029515557149 2860328633574386068333931)
    ·
      refine ⟨4290492950361579102500897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2860328633574386068333931 4290492950361579102500897)
      ·
        refine ⟨3217869712771184326875673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4290492950361579102500897 3217869712771184326875673)
        ·
          refine ⟨2413402284578388245156755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217869712771184326875673 2413402284578388245156755)
          ·
            refine ⟨3620103426867582367735133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413402284578388245156755 3620103426867582367735133)
            ·
              refine ⟨1357538785075343387900675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3620103426867582367735133 1357538785075343387900675)
              ·
                refine ⟨2036308177613015081851013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357538785075343387900675 2036308177613015081851013)
                ·
                  refine ⟨381807783302440327847065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036308177613015081851013 381807783302440327847065)
                  ·
                    rfl

theorem cell20_836514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_836514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836514 prefixEnd_836514 := by exact prefixLift 836514
  have htrace : WordTrace (prefixWord ++ tailWord_836514) baseStart_836514 baseEnd_836514 := by
    simpa [prefixWord, tailWord_836514, baseEnd_836514] using wordTrace_append hprefix tailTrace_836514
  have hstable : (prefixWord ++ tailWord_836514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836514).length < 2 ^ (prefixWord ++ tailWord_836514).sum := by decide
  have hdescent : baseEnd_836514 < baseStart_836514 := by decide
  rcases family_descends (prefixWord ++ tailWord_836514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836542 : List Nat := [4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_836542 : Nat := 118140960795 + 836542 * 2 ^ 59
def prefixEnd_836542 : Nat := 4983230072969 + 3 ^ 40 * 836542 * 2
def baseEnd_836542 : Nat := 127273521088465558304539

theorem tailTrace_836542 : CollatzResearch.WordTrace tailWord_836542 prefixEnd_836542 127273521088465558304539 := by
  unfold tailWord_836542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813899166919834855530985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20340795556905785896165253 3813899166919834855530985)
  ·
    refine ⟨2860424375189876141648239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3813899166919834855530985 2860424375189876141648239)
    ·
      refine ⟨4290636562784814212472359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2860424375189876141648239 4290636562784814212472359)
      ·
        refine ⟨6435954844177221318708539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290636562784814212472359 6435954844177221318708539)
        ·
          refine ⟨9653932266265831978062809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435954844177221318708539 9653932266265831978062809)
          ·
            refine ⟨7240449199699373983547107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9653932266265831978062809 7240449199699373983547107)
            ·
              refine ⟨10860673799549060975320661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240449199699373983547107 10860673799549060975320661)
              ·
                refine ⟨127273521088465558304539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10860673799549060975320661 127273521088465558304539)
                ·
                  rfl

theorem cell20_836542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_836542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836542 prefixEnd_836542 := by exact prefixLift 836542
  have htrace : WordTrace (prefixWord ++ tailWord_836542) baseStart_836542 baseEnd_836542 := by
    simpa [prefixWord, tailWord_836542, baseEnd_836542] using wordTrace_append hprefix tailTrace_836542
  have hstable : (prefixWord ++ tailWord_836542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836542).length < 2 ^ (prefixWord ++ tailWord_836542).sum := by decide
  have hdescent : baseEnd_836542 < baseStart_836542 := by decide
  rcases family_descends (prefixWord ++ tailWord_836542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836565 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 2]
def baseStart_836565 : Nat := 118140960795 + 836565 * 2 ^ 59
def prefixEnd_836565 : Nat := 4983230072969 + 3 ^ 40 * 836565 * 2
def baseEnd_836565 : Nat := 381831061092110817146857

theorem tailTrace_836565 : CollatzResearch.WordTrace tailWord_836565 prefixEnd_836565 381831061092110817146857 := by
  unfold tailWord_836565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30512032214275353772335149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20341354809516902514890099 30512032214275353772335149)
  ·
    refine ⟨11442012080353257664625681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30512032214275353772335149 11442012080353257664625681)
    ·
      refine ⟨8581509060264943248469261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11442012080353257664625681 8581509060264943248469261)
      ·
        refine ⟨3218065897599353718175973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8581509060264943248469261 3218065897599353718175973)
        ·
          refine ⟨603387355799878822157995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3218065897599353718175973 603387355799878822157995)
          ·
            refine ⟨905081033699818233236993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603387355799878822157995 905081033699818233236993)
            ·
              refine ⟨678810775274863674927745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905081033699818233236993 678810775274863674927745)
              ·
                refine ⟨509108081456147756195809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678810775274863674927745 509108081456147756195809)
                ·
                  refine ⟨381831061092110817146857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509108081456147756195809 381831061092110817146857)
                  ·
                    rfl

theorem cell20_836565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_836565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836565 prefixEnd_836565 := by exact prefixLift 836565
  have htrace : WordTrace (prefixWord ++ tailWord_836565) baseStart_836565 baseEnd_836565 := by
    simpa [prefixWord, tailWord_836565, baseEnd_836565] using wordTrace_append hprefix tailTrace_836565
  have hstable : (prefixWord ++ tailWord_836565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836565).length < 2 ^ (prefixWord ++ tailWord_836565).sum := by decide
  have hdescent : baseEnd_836565 < baseStart_836565 := by decide
  rcases family_descends (prefixWord ++ tailWord_836565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836569 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 2]
def baseStart_836569 : Nat := 118140960795 + 836569 * 2 ^ 59
def prefixEnd_836569 : Nat := 4983230072969 + 3 ^ 40 * 836569 * 2
def baseEnd_836569 : Nat := 381832886801104581013507

theorem tailTrace_836569 : CollatzResearch.WordTrace tailWord_836569 prefixEnd_836569 381832886801104581013507 := by
  unfold tailWord_836569
  simp only [CollatzResearch.WordTrace]
  refine ⟨30512178106260862455480761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20341452070840574970320507 30512178106260862455480761)
  ·
    refine ⟨22884133579695646841610571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30512178106260862455480761 22884133579695646841610571)
    ·
      refine ⟨34326200369543470262415857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22884133579695646841610571 34326200369543470262415857)
      ·
        refine ⟨25744650277157602696811893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34326200369543470262415857 25744650277157602696811893)
        ·
          refine ⟨2413560963483525252826115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25744650277157602696811893 2413560963483525252826115)
          ·
            refine ⟨3620341445225287879239173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413560963483525252826115 3620341445225287879239173)
            ·
              refine ⟨678814020979741477357345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3620341445225287879239173 678814020979741477357345)
              ·
                refine ⟨509110515734806108018009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678814020979741477357345 509110515734806108018009)
                ·
                  refine ⟨381832886801104581013507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509110515734806108018009 381832886801104581013507)
                  ·
                    rfl

theorem cell20_836569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_836569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836569 prefixEnd_836569 := by exact prefixLift 836569
  have htrace : WordTrace (prefixWord ++ tailWord_836569) baseStart_836569 baseEnd_836569 := by
    simpa [prefixWord, tailWord_836569, baseEnd_836569] using wordTrace_append hprefix tailTrace_836569
  have hstable : (prefixWord ++ tailWord_836569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836569).length < 2 ^ (prefixWord ++ tailWord_836569).sum := by decide
  have hdescent : baseEnd_836569 < baseStart_836569 := by decide
  rcases family_descends (prefixWord ++ tailWord_836569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836590 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_836590 : Nat := 118140960795 + 836590 * 2 ^ 59
def prefixEnd_836590 : Nat := 4983230072969 + 3 ^ 40 * 836590 * 2
def baseEnd_836590 : Nat := 381842471773321841313421

theorem tailTrace_836590 : CollatzResearch.WordTrace tailWord_836590 prefixEnd_836590 381842471773321841313421 := by
  unfold tailWord_836590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814118004898097880249403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20341962692789855361330149 3814118004898097880249403)
  ·
    refine ⟨5721177007347146820374105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3814118004898097880249403 5721177007347146820374105)
    ·
      refine ⟨4290882755510360115280579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5721177007347146820374105 4290882755510360115280579)
      ·
        refine ⟨6436324133265540172920869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290882755510360115280579 6436324133265540172920869)
        ·
          refine ⟨1206810774987288782422663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6436324133265540172920869 1206810774987288782422663)
          ·
            refine ⟨1810216162480933173633995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206810774987288782422663 1810216162480933173633995)
            ·
              refine ⟨2715324243721399760450993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810216162480933173633995 2715324243721399760450993)
              ·
                refine ⟨2036493182791049820338245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715324243721399760450993 2036493182791049820338245)
                ·
                  refine ⟨381842471773321841313421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036493182791049820338245 381842471773321841313421)
                  ·
                    rfl

theorem cell20_836590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_836590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836590 prefixEnd_836590 := by exact prefixLift 836590
  have htrace : WordTrace (prefixWord ++ tailWord_836590) baseStart_836590 baseEnd_836590 := by
    simpa [prefixWord, tailWord_836590, baseEnd_836590] using wordTrace_append hprefix tailTrace_836590
  have hstable : (prefixWord ++ tailWord_836590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836590).length < 2 ^ (prefixWord ++ tailWord_836590).sum := by decide
  have hdescent : baseEnd_836590 < baseStart_836590 := by decide
  rcases family_descends (prefixWord ++ tailWord_836590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836618 : List Nat := [3, 1, 2, 2, 3, 2, 7]
def baseStart_836618 : Nat := 118140960795 + 836618 * 2 ^ 59
def prefixEnd_836618 : Nat := 4983230072969 + 3 ^ 40 * 836618 * 2
def baseEnd_836618 : Nat := 42428361304030909819997

theorem tailTrace_836618 : CollatzResearch.WordTrace tailWord_836618 prefixEnd_836618 42428361304030909819997 := by
  unfold tailWord_836618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628491320770835956003627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20342643522055562549343005 7628491320770835956003627)
  ·
    refine ⟨11442736981156253934005441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628491320770835956003627 11442736981156253934005441)
    ·
      refine ⟨8582052735867190450504081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11442736981156253934005441 8582052735867190450504081)
      ·
        refine ⟨6436539551900392837878061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8582052735867190450504081 6436539551900392837878061)
        ·
          refine ⟨2413702331962647314204273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6436539551900392837878061 2413702331962647314204273)
          ·
            refine ⟨1810276748971985485653205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413702331962647314204273 1810276748971985485653205)
            ·
              refine ⟨42428361304030909819997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1810276748971985485653205 42428361304030909819997)
              ·
                rfl

theorem cell20_836618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_836618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836618 prefixEnd_836618 := by exact prefixLift 836618
  have htrace : WordTrace (prefixWord ++ tailWord_836618) baseStart_836618 baseEnd_836618 := by
    simpa [prefixWord, tailWord_836618, baseEnd_836618] using wordTrace_append hprefix tailTrace_836618
  have hstable : (prefixWord ++ tailWord_836618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836618).length < 2 ^ (prefixWord ++ tailWord_836618).sum := by decide
  have hdescent : baseEnd_836618 < baseStart_836618 := by decide
  rcases family_descends (prefixWord ++ tailWord_836618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836662 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_836662 : Nat := 118140960795 + 836662 * 2 ^ 59
def prefixEnd_836662 : Nat := 4983230072969 + 3 ^ 40 * 836662 * 2
def baseEnd_836662 : Nat := 381875334535209590913127

theorem tailTrace_836662 : CollatzResearch.WordTrace tailWord_836662 prefixEnd_836662 381875334535209590913127 := by
  unfold tailWord_836662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907223130932746208663515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20343713396615959559077493 1907223130932746208663515)
  ·
    refine ⟨2860834696399119312995273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1907223130932746208663515 2860834696399119312995273)
    ·
      refine ⟨2145626022299339484746455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2860834696399119312995273 2145626022299339484746455)
      ·
        refine ⟨3218439033449009227119683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145626022299339484746455 3218439033449009227119683)
        ·
          refine ⟨4827658550173513840679525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218439033449009227119683 4827658550173513840679525)
          ·
            refine ⟨905185978157533845127411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4827658550173513840679525 905185978157533845127411)
            ·
              refine ⟨1357778967236300767691117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905185978157533845127411 1357778967236300767691117)
              ·
                refine ⟨509167112713612787884169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1357778967236300767691117 509167112713612787884169)
                ·
                  refine ⟨381875334535209590913127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509167112713612787884169 381875334535209590913127)
                  ·
                    rfl

theorem cell20_836662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_836662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836662 prefixEnd_836662 := by exact prefixLift 836662
  have htrace : WordTrace (prefixWord ++ tailWord_836662) baseStart_836662 baseEnd_836662 := by
    simpa [prefixWord, tailWord_836662, baseEnd_836662] using wordTrace_append hprefix tailTrace_836662
  have hstable : (prefixWord ++ tailWord_836662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836662).length < 2 ^ (prefixWord ++ tailWord_836662).sum := by decide
  have hdescent : baseEnd_836662 < baseStart_836662 := by decide
  rcases family_descends (prefixWord ++ tailWord_836662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836666 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_836666 : Nat := 118140960795 + 836666 * 2 ^ 59
def prefixEnd_836666 : Nat := 4983230072969 + 3 ^ 40 * 836666 * 2
def baseEnd_836666 : Nat := 381877160244203354779777

theorem tailTrace_836666 : CollatzResearch.WordTrace tailWord_836666 prefixEnd_836666 381877160244203354779777 := by
  unfold tailWord_836666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628928996727362005440463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20343810657939632014507901 7628928996727362005440463)
  ·
    refine ⟨11443393495091043008160695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628928996727362005440463 11443393495091043008160695)
    ·
      refine ⟨17165090242636564512241043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11443393495091043008160695 17165090242636564512241043)
      ·
        refine ⟨25747635363954846768361565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17165090242636564512241043 25747635363954846768361565)
        ·
          refine ⟨9655363261483067538135587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25747635363954846768361565 9655363261483067538135587)
          ·
            refine ⟨14483044892224601307203381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9655363261483067538135587 14483044892224601307203381)
            ·
              refine ⟨1357785458646056372550317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14483044892224601307203381 1357785458646056372550317)
              ·
                refine ⟨509169546992271139706369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1357785458646056372550317 509169546992271139706369)
                ·
                  refine ⟨381877160244203354779777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509169546992271139706369 381877160244203354779777)
                  ·
                    rfl

theorem cell20_836666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_836666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836666 prefixEnd_836666 := by exact prefixLift 836666
  have htrace : WordTrace (prefixWord ++ tailWord_836666) baseStart_836666 baseEnd_836666 := by
    simpa [prefixWord, tailWord_836666, baseEnd_836666] using wordTrace_append hprefix tailTrace_836666
  have hstable : (prefixWord ++ tailWord_836666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836666).length < 2 ^ (prefixWord ++ tailWord_836666).sum := by decide
  have hdescent : baseEnd_836666 < baseStart_836666 := by decide
  rcases family_descends (prefixWord ++ tailWord_836666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836673 : List Nat := [1, 2, 5, 1, 3, 2, 6]
def baseStart_836673 : Nat := 118140960795 + 836673 * 2 ^ 59
def prefixEnd_836673 : Nat := 4983230072969 + 3 ^ 40 * 836673 * 2
def baseEnd_836673 : Nat := 42431150581660271282935

theorem tailTrace_836673 : CollatzResearch.WordTrace tailWord_836673 prefixEnd_836673 42431150581660271282935 := by
  unfold tailWord_836673
  simp only [CollatzResearch.WordTrace]
  refine ⟨30515971297884088217266673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20343980865256058811511115 30515971297884088217266673)
  ·
    refine ⟨22886978473413066162950005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30515971297884088217266673 22886978473413066162950005)
    ·
      refine ⟨2145654231882474952776563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22886978473413066162950005 2145654231882474952776563)
      ·
        refine ⟨3218481347823712429164845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145654231882474952776563 3218481347823712429164845)
        ·
          refine ⟨1206930505433892160936817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3218481347823712429164845 1206930505433892160936817)
          ·
            refine ⟨905197879075419120702613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206930505433892160936817 905197879075419120702613)
            ·
              refine ⟨42431150581660271282935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 905197879075419120702613 42431150581660271282935)
              ·
                rfl

theorem cell20_836673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_836673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836673 prefixEnd_836673 := by exact prefixLift 836673
  have htrace : WordTrace (prefixWord ++ tailWord_836673) baseStart_836673 baseEnd_836673 := by
    simpa [prefixWord, tailWord_836673, baseEnd_836673] using wordTrace_append hprefix tailTrace_836673
  have hstable : (prefixWord ++ tailWord_836673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836673).length < 2 ^ (prefixWord ++ tailWord_836673).sum := by decide
  have hdescent : baseEnd_836673 < baseStart_836673 := by decide
  rcases family_descends (prefixWord ++ tailWord_836673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836677 : List Nat := [1, 3, 1, 1, 1, 3, 10]
def baseStart_836677 : Nat := 118140960795 + 836677 * 2 ^ 59
def prefixEnd_836677 : Nat := 4983230072969 + 3 ^ 40 * 836677 * 2
def baseEnd_836677 : Nat := 42431353438215133934785

theorem tailTrace_836677 : CollatzResearch.WordTrace tailWord_836677 prefixEnd_836677 42431353438215133934785 := by
  unfold tailWord_836677
  simp only [CollatzResearch.WordTrace]
  refine ⟨30516117189869596900412285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20344078126579731266941523 30516117189869596900412285)
  ·
    refine ⟨11443543946201098837654607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30516117189869596900412285 11443543946201098837654607)
    ·
      refine ⟨17165315919301648256481911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11443543946201098837654607 17165315919301648256481911)
      ·
        refine ⟨25747973878952472384722867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17165315919301648256481911 25747973878952472384722867)
        ·
          refine ⟨38621960818428708577084301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25747973878952472384722867 38621960818428708577084301)
          ·
            refine ⟨14483235306910765716406613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38621960818428708577084301 14483235306910765716406613)
            ·
              refine ⟨42431353438215133934785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14483235306910765716406613 42431353438215133934785)
              ·
                rfl

theorem cell20_836677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_836677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836677 prefixEnd_836677 := by exact prefixLift 836677
  have htrace : WordTrace (prefixWord ++ tailWord_836677) baseStart_836677 baseEnd_836677 := by
    simpa [prefixWord, tailWord_836677, baseEnd_836677] using wordTrace_append hprefix tailTrace_836677
  have hstable : (prefixWord ++ tailWord_836677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836677).length < 2 ^ (prefixWord ++ tailWord_836677).sum := by decide
  have hdescent : baseEnd_836677 < baseStart_836677 := by decide
  rcases family_descends (prefixWord ++ tailWord_836677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836708 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_836708 : Nat := 118140960795 + 836708 * 2 ^ 59
def prefixEnd_836708 : Nat := 4983230072969 + 3 ^ 40 * 836708 * 2
def baseEnd_836708 : Nat := 381896330188637875379605

theorem tailTrace_836708 : CollatzResearch.WordTrace tailWord_836708 prefixEnd_836708 381896330188637875379605 := by
  unfold tailWord_836708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258623926378644597395389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20344831901838192796527185 15258623926378644597395389)
  ·
    refine ⟨5721983972391991724023271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15258623926378644597395389 5721983972391991724023271)
    ·
      refine ⟨8582975958587987586034907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5721983972391991724023271 8582975958587987586034907)
      ·
        refine ⟨12874463937881981379052361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8582975958587987586034907 12874463937881981379052361)
        ·
          refine ⟨9655847953411486034289271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12874463937881981379052361 9655847953411486034289271)
          ·
            refine ⟨14483771930117229051433907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9655847953411486034289271 14483771930117229051433907)
            ·
              refine ⟨21725657895175843577150861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14483771930117229051433907 21725657895175843577150861)
              ·
                refine ⟨8147121710690941341431573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21725657895175843577150861 8147121710690941341431573)
                ·
                  refine ⟨381896330188637875379605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8147121710690941341431573 381896330188637875379605)
                  ·
                    rfl

theorem cell20_836708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_836708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836708 prefixEnd_836708 := by exact prefixLift 836708
  have htrace : WordTrace (prefixWord ++ tailWord_836708) baseStart_836708 baseEnd_836708 := by
    simpa [prefixWord, tailWord_836708, baseEnd_836708] using wordTrace_append hprefix tailTrace_836708
  have hstable : (prefixWord ++ tailWord_836708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836708).length < 2 ^ (prefixWord ++ tailWord_836708).sum := by decide
  have hdescent : baseEnd_836708 < baseStart_836708 := by decide
  rcases family_descends (prefixWord ++ tailWord_836708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836766 : List Nat := [4, 3, 1, 1, 2, 2, 3, 4]
def baseStart_836766 : Nat := 118140960795 + 836766 * 2 ^ 59
def prefixEnd_836766 : Nat := 4983230072969 + 3 ^ 40 * 836766 * 2
def baseEnd_836766 : Nat := 127307600989682483815345

theorem tailTrace_836766 : CollatzResearch.WordTrace tailWord_836766 prefixEnd_836766 127307600989682483815345 := by
  unfold tailWord_836766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814920410818395637550269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20346242191031443400268101 3814920410818395637550269)
  ·
    refine ⟨1430595154056898364081351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3814920410818395637550269 1430595154056898364081351)
    ·
      refine ⟨2145892731085347546122027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430595154056898364081351 2145892731085347546122027)
      ·
        refine ⟨3218839096628021319183041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145892731085347546122027 3218839096628021319183041)
        ·
          refine ⟨2414129322471015989387281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3218839096628021319183041 2414129322471015989387281)
          ·
            refine ⟨1810596991853261992040461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414129322471015989387281 1810596991853261992040461)
            ·
              refine ⟨678973871944973247015173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1810596991853261992040461 678973871944973247015173)
              ·
                refine ⟨127307600989682483815345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678973871944973247015173 127307600989682483815345)
                ·
                  rfl

theorem cell20_836766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_836766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836766 prefixEnd_836766 := by exact prefixLift 836766
  have htrace : WordTrace (prefixWord ++ tailWord_836766) baseStart_836766 baseEnd_836766 := by
    simpa [prefixWord, tailWord_836766, baseEnd_836766] using wordTrace_append hprefix tailTrace_836766
  have hstable : (prefixWord ++ tailWord_836766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836766).length < 2 ^ (prefixWord ++ tailWord_836766).sum := by decide
  have hdescent : baseEnd_836766 < baseStart_836766 := by decide
  rcases family_descends (prefixWord ++ tailWord_836766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836790 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_836790 : Nat := 118140960795 + 836790 * 2 ^ 59
def prefixEnd_836790 : Nat := 4983230072969 + 3 ^ 40 * 836790 * 2
def baseEnd_836790 : Nat := 381933757223010034645937

theorem tailTrace_836790 : CollatzResearch.WordTrace tailWord_836790 prefixEnd_836790 381933757223010034645937 := by
  unfold tailWord_836790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907514914903763574954739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20346825758973478132850549 1907514914903763574954739)
  ·
    refine ⟨2861272372355645362432109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1907514914903763574954739 2861272372355645362432109)
    ·
      refine ⟨1072977139633367010912041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2861272372355645362432109 1072977139633367010912041)
      ·
        refine ⟨804732854725025258184031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072977139633367010912041 804732854725025258184031)
        ·
          refine ⟨1207099282087537887276047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804732854725025258184031 1207099282087537887276047)
          ·
            refine ⟨1810648923131306830914071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207099282087537887276047 1810648923131306830914071)
            ·
              refine ⟨2715973384696960246371107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810648923131306830914071 2715973384696960246371107)
              ·
                refine ⟨4073960077045440369556661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715973384696960246371107 4073960077045440369556661)
                ·
                  refine ⟨381933757223010034645937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4073960077045440369556661 381933757223010034645937)
                  ·
                    rfl

theorem cell20_836790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_836790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836790 prefixEnd_836790 := by exact prefixLift 836790
  have htrace : WordTrace (prefixWord ++ tailWord_836790) baseStart_836790 baseEnd_836790 := by
    simpa [prefixWord, tailWord_836790, baseEnd_836790] using wordTrace_append hprefix tailTrace_836790
  have hstable : (prefixWord ++ tailWord_836790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836790).length < 2 ^ (prefixWord ++ tailWord_836790).sum := by decide
  have hdescent : baseEnd_836790 < baseStart_836790 := by decide
  rcases family_descends (prefixWord ++ tailWord_836790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836791 : List Nat := [1, 1, 3, 1, 4, 1, 9]
def baseStart_836791 : Nat := 118140960795 + 836791 * 2 ^ 59
def prefixEnd_836791 : Nat := 4983230072969 + 3 ^ 40 * 836791 * 2
def baseEnd_836791 : Nat := 42437134850028719512511

theorem tailTrace_836791 : CollatzResearch.WordTrace tailWord_836791 prefixEnd_836791 42437134850028719512511 := by
  unfold tailWord_836791
  simp only [CollatzResearch.WordTrace]
  refine ⟨30520275111456594370062227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20346850074304396246708151 30520275111456594370062227)
  ·
    refine ⟨45780412667184891555093341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30520275111456594370062227 45780412667184891555093341)
    ·
      refine ⟨17167654750194334333160003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45780412667184891555093341 17167654750194334333160003)
      ·
        refine ⟨25751482125291501499740005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17167654750194334333160003 25751482125291501499740005)
        ·
          refine ⟨4828402898492156531201251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25751482125291501499740005 4828402898492156531201251)
          ·
            refine ⟨7242604347738234796801877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828402898492156531201251 7242604347738234796801877)
            ·
              refine ⟨42437134850028719512511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7242604347738234796801877 42437134850028719512511)
              ·
                rfl

theorem cell20_836791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_836791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836791 prefixEnd_836791 := by exact prefixLift 836791
  have htrace : WordTrace (prefixWord ++ tailWord_836791) baseStart_836791 baseEnd_836791 := by
    simpa [prefixWord, tailWord_836791, baseEnd_836791] using wordTrace_append hprefix tailTrace_836791
  have hstable : (prefixWord ++ tailWord_836791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836791).length < 2 ^ (prefixWord ++ tailWord_836791).sum := by decide
  have hdescent : baseEnd_836791 < baseStart_836791 := by decide
  rcases family_descends (prefixWord ++ tailWord_836791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836867 : List Nat := [1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_836867 : Nat := 118140960795 + 836867 * 2 ^ 59
def prefixEnd_836867 : Nat := 4983230072969 + 3 ^ 40 * 836867 * 2
def baseEnd_836867 : Nat := 127322967373713329692985

theorem tailTrace_836867 : CollatzResearch.WordTrace tailWord_836867 prefixEnd_836867 127322967373713329692985 := by
  unfold tailWord_836867
  simp only [CollatzResearch.WordTrace]
  refine ⟨30523047059181259349828855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20348698039454172899885903 30523047059181259349828855)
  ·
    refine ⟨45784570588771889024743283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30523047059181259349828855 45784570588771889024743283)
    ·
      refine ⟨68676855883157833537114925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45784570588771889024743283 68676855883157833537114925)
      ·
        refine ⟨25753820956184187576418097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68676855883157833537114925 25753820956184187576418097)
        ·
          refine ⟨19315365717138140682313573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25753820956184187576418097 19315365717138140682313573)
          ·
            refine ⟨3621631071963401377933795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19315365717138140682313573 3621631071963401377933795)
            ·
              refine ⟨5432446607945102066900693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621631071963401377933795 5432446607945102066900693)
              ·
                refine ⟨127322967373713329692985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5432446607945102066900693 127322967373713329692985)
                ·
                  rfl

theorem cell20_836867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_836867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836867 prefixEnd_836867 := by exact prefixLift 836867
  have htrace : WordTrace (prefixWord ++ tailWord_836867) baseStart_836867 baseEnd_836867 := by
    simpa [prefixWord, tailWord_836867, baseEnd_836867] using wordTrace_append hprefix tailTrace_836867
  have hstable : (prefixWord ++ tailWord_836867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836867).length < 2 ^ (prefixWord ++ tailWord_836867).sum := by decide
  have hdescent : baseEnd_836867 < baseStart_836867 := by decide
  rcases family_descends (prefixWord ++ tailWord_836867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836932 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_836932 : Nat := 118140960795 + 836932 * 2 ^ 59
def prefixEnd_836932 : Nat := 4983230072969 + 3 ^ 40 * 836932 * 2
def baseEnd_836932 : Nat := 381998569892288651912023

theorem tailTrace_836932 : CollatzResearch.WordTrace tailWord_836932 prefixEnd_836932 381998569892288651912023 := by
  unfold tailWord_836932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15262708901972887725472525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20350278535963850300630033 15262708901972887725472525)
  ·
    refine ⟨5723515838239832897052197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15262708901972887725472525 5723515838239832897052197)
    ·
      refine ⟨1073159219669968668197287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5723515838239832897052197 1073159219669968668197287)
      ·
        refine ⟨1609738829504953002295931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073159219669968668197287 1609738829504953002295931)
        ·
          refine ⟨2414608244257429503443897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609738829504953002295931 2414608244257429503443897)
          ·
            refine ⟨1810956183193072127582923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414608244257429503443897 1810956183193072127582923)
            ·
              refine ⟨2716434274789608191374385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810956183193072127582923 2716434274789608191374385)
              ·
                refine ⟨2037325706092206143530789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716434274789608191374385 2037325706092206143530789)
                ·
                  refine ⟨381998569892288651912023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2037325706092206143530789 381998569892288651912023)
                  ·
                    rfl

theorem cell20_836932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_836932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836932 prefixEnd_836932 := by exact prefixLift 836932
  have htrace : WordTrace (prefixWord ++ tailWord_836932) baseStart_836932 baseEnd_836932 := by
    simpa [prefixWord, tailWord_836932, baseEnd_836932] using wordTrace_append hprefix tailTrace_836932
  have hstable : (prefixWord ++ tailWord_836932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836932).length < 2 ^ (prefixWord ++ tailWord_836932).sum := by decide
  have hdescent : baseEnd_836932 < baseStart_836932 := by decide
  rcases family_descends (prefixWord ++ tailWord_836932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836953 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 2]
def baseStart_836953 : Nat := 118140960795 + 836953 * 2 ^ 59
def prefixEnd_836953 : Nat := 4983230072969 + 3 ^ 40 * 836953 * 2
def baseEnd_836953 : Nat := 382008154864505912211937

theorem tailTrace_836953 : CollatzResearch.WordTrace tailWord_836953 prefixEnd_836953 382008154864505912211937 := by
  unfold tailWord_836953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526183736869696037459513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20350789157913130691639675 30526183736869696037459513)
  ·
    refine ⟨22894637802652272028094635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30526183736869696037459513 22894637802652272028094635)
    ·
      refine ⟨34341956703978408042141953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22894637802652272028094635 34341956703978408042141953)
      ·
        refine ⟨25756467527983806031606465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34341956703978408042141953 25756467527983806031606465)
        ·
          refine ⟨19317350645987854523704849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25756467527983806031606465 19317350645987854523704849)
          ·
            refine ⟨14488012984490890892778637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19317350645987854523704849 14488012984490890892778637)
            ·
              refine ⟨5433004869184084084791989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14488012984490890892778637 5433004869184084084791989)
              ·
                refine ⟨509344206486007882949249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5433004869184084084791989 509344206486007882949249)
                ·
                  refine ⟨382008154864505912211937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509344206486007882949249 382008154864505912211937)
                  ·
                    rfl

theorem cell20_836953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_836953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836953 prefixEnd_836953 := by exact prefixLift 836953
  have htrace : WordTrace (prefixWord ++ tailWord_836953) baseStart_836953 baseEnd_836953 := by
    simpa [prefixWord, tailWord_836953, baseEnd_836953] using wordTrace_append hprefix tailTrace_836953
  have hstable : (prefixWord ++ tailWord_836953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836953).length < 2 ^ (prefixWord ++ tailWord_836953).sum := by decide
  have hdescent : baseEnd_836953 < baseStart_836953 := by decide
  rcases family_descends (prefixWord ++ tailWord_836953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836970 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_836970 : Nat := 118140960795 + 836970 * 2 ^ 59
def prefixEnd_836970 : Nat := 4983230072969 + 3 ^ 40 * 836970 * 2
def baseEnd_836970 : Nat := 382015914127729408645201

theorem tailTrace_836970 : CollatzResearch.WordTrace tailWord_836970 prefixEnd_836970 382015914127729408645201 := by
  unfold tailWord_836970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631700944452026985207091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20351202518538738627218909 7631700944452026985207091)
  ·
    refine ⟨11447551416678040477810637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7631700944452026985207091 11447551416678040477810637)
    ·
      refine ⟨4292831781254265179178989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11447551416678040477810637 4292831781254265179178989)
      ·
        refine ⟨1609811917970349442192121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4292831781254265179178989 1609811917970349442192121)
        ·
          refine ⟨1207358938477762081644091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609811917970349442192121 1207358938477762081644091)
          ·
            refine ⟨1811038407716643122466137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207358938477762081644091 1811038407716643122466137)
            ·
              refine ⟨1358278805787482341849603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811038407716643122466137 1358278805787482341849603)
              ·
                refine ⟨2037418208681223512774405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358278805787482341849603 2037418208681223512774405)
                ·
                  refine ⟨382015914127729408645201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2037418208681223512774405 382015914127729408645201)
                  ·
                    rfl

theorem cell20_836970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_836970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836970 prefixEnd_836970 := by exact prefixLift 836970
  have htrace : WordTrace (prefixWord ++ tailWord_836970) baseStart_836970 baseEnd_836970 := by
    simpa [prefixWord, tailWord_836970, baseEnd_836970] using wordTrace_append hprefix tailTrace_836970
  have hstable : (prefixWord ++ tailWord_836970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836970).length < 2 ^ (prefixWord ++ tailWord_836970).sum := by decide
  have hdescent : baseEnd_836970 < baseStart_836970 := by decide
  rcases family_descends (prefixWord ++ tailWord_836970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836990 : List Nat := [4, 2, 3, 2, 2, 1, 2, 4]
def baseStart_836990 : Nat := 118140960795 + 836990 * 2 ^ 59
def prefixEnd_836990 : Nat := 4983230072969 + 3 ^ 40 * 836990 * 2
def baseEnd_836990 : Nat := 127341680890899409326151

theorem tailTrace_836990 : CollatzResearch.WordTrace tailWord_836990 prefixEnd_836990 127341680890899409326151 := by
  unfold tailWord_836990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815941654716956419569553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20351688825157100904370949 3815941654716956419569553)
  ·
    refine ⟨2861956241037717314677165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3815941654716956419569553 2861956241037717314677165)
    ·
      refine ⟨1073233590389143993003937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2861956241037717314677165 1073233590389143993003937)
      ·
        refine ⟨804925192791857994752953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1073233590389143993003937 804925192791857994752953)
        ·
          refine ⟨603693894593893496064715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804925192791857994752953 603693894593893496064715)
          ·
            refine ⟨905540841890840244097073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603693894593893496064715 905540841890840244097073)
            ·
              refine ⟨679155631418130183072805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905540841890840244097073 679155631418130183072805)
              ·
                refine ⟨127341680890899409326151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679155631418130183072805 127341680890899409326151)
                ·
                  rfl

theorem cell20_836990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_836990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836990 prefixEnd_836990 := by exact prefixLift 836990
  have htrace : WordTrace (prefixWord ++ tailWord_836990) baseStart_836990 baseEnd_836990 := by
    simpa [prefixWord, tailWord_836990, baseEnd_836990] using wordTrace_append hprefix tailTrace_836990
  have hstable : (prefixWord ++ tailWord_836990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836990).length < 2 ^ (prefixWord ++ tailWord_836990).sum := by decide
  have hdescent : baseEnd_836990 < baseStart_836990 := by decide
  rcases family_descends (prefixWord ++ tailWord_836990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836994 : List Nat := [3, 4, 2, 1, 1, 1, 4, 4]
def baseStart_836994 : Nat := 118140960795 + 836994 * 2 ^ 59
def prefixEnd_836994 : Nat := 4983230072969 + 3 ^ 40 * 836994 * 2
def baseEnd_836994 : Nat := 127342289460563997281701

theorem tailTrace_836994 : CollatzResearch.WordTrace tailWord_836994 prefixEnd_836994 127342289460563997281701 := by
  unfold tailWord_836994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631919782430290009925509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20351786086480773359801357 7631919782430290009925509)
  ·
    refine ⟨1430984959205679376861033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7631919782430290009925509 1430984959205679376861033)
    ·
      refine ⟨1073238719404259532645775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430984959205679376861033 1073238719404259532645775)
      ·
        refine ⟨1609858079106389298968663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073238719404259532645775 1609858079106389298968663)
        ·
          refine ⟨2414787118659583948452995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609858079106389298968663 2414787118659583948452995)
          ·
            refine ⟨3622180677989375922679493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414787118659583948452995 3622180677989375922679493)
            ·
              refine ⟨679158877123007985502405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3622180677989375922679493 679158877123007985502405)
              ·
                refine ⟨127342289460563997281701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679158877123007985502405 127342289460563997281701)
                ·
                  rfl

theorem cell20_836994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_836994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_836994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_836994 prefixEnd_836994 := by exact prefixLift 836994
  have htrace : WordTrace (prefixWord ++ tailWord_836994) baseStart_836994 baseEnd_836994 := by
    simpa [prefixWord, tailWord_836994, baseEnd_836994] using wordTrace_append hprefix tailTrace_836994
  have hstable : (prefixWord ++ tailWord_836994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836994).length < 2 ^ (prefixWord ++ tailWord_836994).sum := by decide
  have hdescent : baseEnd_836994 < baseStart_836994 := by decide
  rcases family_descends (prefixWord ++ tailWord_836994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837081 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_837081 : Nat := 118140960795 + 837081 * 2 ^ 59
def prefixEnd_837081 : Nat := 4983230072969 + 3 ^ 40 * 837081 * 2
def baseEnd_837081 : Nat := 382066577552306355944747

theorem tailTrace_837081 : CollatzResearch.WordTrace tailWord_837081 prefixEnd_837081 382066577552306355944747 := by
  unfold tailWord_837081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30530852280405973898119097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20353901520270649265412731 30530852280405973898119097)
  ·
    refine ⟨22898139210304480423589323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30530852280405973898119097 22898139210304480423589323)
    ·
      refine ⟨34347208815456720635383985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22898139210304480423589323 34347208815456720635383985)
      ·
        refine ⟨25760406611592540476537989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34347208815456720635383985 25760406611592540476537989)
        ·
          refine ⟨4830076239673601339350873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25760406611592540476537989 4830076239673601339350873)
          ·
            refine ⟨3622557179755201004513155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830076239673601339350873 3622557179755201004513155)
            ·
              refine ⟨5433835769632801506769733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622557179755201004513155 5433835769632801506769733)
              ·
                refine ⟨1018844206806150282519325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5433835769632801506769733 1018844206806150282519325)
                ·
                  refine ⟨382066577552306355944747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018844206806150282519325 382066577552306355944747)
                  ·
                    rfl

theorem cell20_837081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_837081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837081 prefixEnd_837081 := by exact prefixLift 837081
  have htrace : WordTrace (prefixWord ++ tailWord_837081) baseStart_837081 baseEnd_837081 := by
    simpa [prefixWord, tailWord_837081, baseEnd_837081] using wordTrace_append hprefix tailTrace_837081
  have hstable : (prefixWord ++ tailWord_837081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837081).length < 2 ^ (prefixWord ++ tailWord_837081).sum := by decide
  have hdescent : baseEnd_837081 < baseStart_837081 := by decide
  rcases family_descends (prefixWord ++ tailWord_837081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837112 : List Nat := [2, 1, 2, 1, 1, 6, 3, 4]
def baseStart_837112 : Nat := 118140960795 + 837112 * 2 ^ 59
def prefixEnd_837112 : Nat := 4983230072969 + 3 ^ 40 * 837112 * 2
def baseEnd_837112 : Nat := 127360242265669341970429

theorem tailTrace_837112 : CollatzResearch.WordTrace tailWord_837112 prefixEnd_837112 127360242265669341970429 := by
  unfold tailWord_837112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265991471646833096248795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20354655295529110794998393 15265991471646833096248795)
  ·
    refine ⟨22898987207470249644373193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15265991471646833096248795 22898987207470249644373193)
    ·
      refine ⟨17174240405602687233279895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22898987207470249644373193 17174240405602687233279895)
      ·
        refine ⟨25761360608404030849919843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17174240405602687233279895 25761360608404030849919843)
        ·
          refine ⟨38642040912606046274879765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25761360608404030849919843 38642040912606046274879765)
          ·
            refine ⟨1811345667778408419134989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38642040912606046274879765 1811345667778408419134989)
            ·
              refine ⟨679254625416903157175621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811345667778408419134989 679254625416903157175621)
              ·
                refine ⟨127360242265669341970429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679254625416903157175621 127360242265669341970429)
                ·
                  rfl

theorem cell20_837112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_837112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837112 prefixEnd_837112 := by exact prefixLift 837112
  have htrace : WordTrace (prefixWord ++ tailWord_837112) baseStart_837112 baseEnd_837112 := by
    simpa [prefixWord, tailWord_837112, baseEnd_837112] using wordTrace_append hprefix tailTrace_837112
  have hstable : (prefixWord ++ tailWord_837112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837112).length < 2 ^ (prefixWord ++ tailWord_837112).sum := by decide
  have hdescent : baseEnd_837112 < baseStart_837112 := by decide
  rcases family_descends (prefixWord ++ tailWord_837112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837118 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_837118 : Nat := 118140960795 + 837118 * 2 ^ 59
def prefixEnd_837118 : Nat := 4983230072969 + 3 ^ 40 * 837118 * 2
def baseEnd_837118 : Nat := 382083465360498671711263

theorem tailTrace_837118 : CollatzResearch.WordTrace tailWord_837118 prefixEnd_837118 382083465360498671711263 := by
  unfold tailWord_837118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816525222658991152152001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20354801187514619478144005 3816525222658991152152001)
  ·
    refine ⟨2862393916994243364114001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3816525222658991152152001 2862393916994243364114001)
    ·
      refine ⟨2146795437745682523085501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2862393916994243364114001 2146795437745682523085501)
      ·
        refine ⟨805048289154630946157063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2146795437745682523085501 805048289154630946157063)
        ·
          refine ⟨1207572433731946419235595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805048289154630946157063 1207572433731946419235595)
          ·
            refine ⟨1811358650597919628853393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207572433731946419235595 1811358650597919628853393)
            ·
              refine ⟨1358518987948439721640045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811358650597919628853393 1358518987948439721640045)
              ·
                refine ⟨509444620480664895615017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358518987948439721640045 509444620480664895615017)
                ·
                  refine ⟨382083465360498671711263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509444620480664895615017 382083465360498671711263)
                  ·
                    rfl

theorem cell20_837118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_837118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837118 prefixEnd_837118 := by exact prefixLift 837118
  have htrace : WordTrace (prefixWord ++ tailWord_837118) baseStart_837118 baseEnd_837118 := by
    simpa [prefixWord, tailWord_837118, baseEnd_837118] using wordTrace_append hprefix tailTrace_837118
  have hstable : (prefixWord ++ tailWord_837118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837118).length < 2 ^ (prefixWord ++ tailWord_837118).sum := by decide
  have hdescent : baseEnd_837118 < baseStart_837118 := by decide
  rcases family_descends (prefixWord ++ tailWord_837118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837171 : List Nat := [1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_837171 : Nat := 118140960795 + 837171 * 2 ^ 59
def prefixEnd_837171 : Nat := 4983230072969 + 3 ^ 40 * 837171 * 2
def baseEnd_837171 : Nat := 127369218668222014314793

theorem tailTrace_837171 : CollatzResearch.WordTrace tailWord_837171 prefixEnd_837171 127369218668222014314793 := by
  unfold tailWord_837171
  simp only [CollatzResearch.WordTrace]
  refine ⟨30534134850079919268895367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20356089900053279512596911 30534134850079919268895367)
  ·
    refine ⟨45801202275119878903343051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30534134850079919268895367 45801202275119878903343051)
    ·
      refine ⟨68701803412679818355014577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45801202275119878903343051 68701803412679818355014577)
      ·
        refine ⟨51526352559509863766260933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68701803412679818355014577 51526352559509863766260933)
        ·
          refine ⟨9661191104908099456173925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51526352559509863766260933 9661191104908099456173925)
          ·
            refine ⟨1811473332170268648032611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9661191104908099456173925 1811473332170268648032611)
            ·
              refine ⟨2717209998255402972048917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811473332170268648032611 2717209998255402972048917)
              ·
                refine ⟨127369218668222014314793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2717209998255402972048917 127369218668222014314793)
                ·
                  rfl

theorem cell20_837171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_837171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837171 prefixEnd_837171 := by exact prefixLift 837171
  have htrace : WordTrace (prefixWord ++ tailWord_837171) baseStart_837171 baseEnd_837171 := by
    simpa [prefixWord, tailWord_837171, baseEnd_837171] using wordTrace_append hprefix tailTrace_837171
  have hstable : (prefixWord ++ tailWord_837171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837171).length < 2 ^ (prefixWord ++ tailWord_837171).sum := by decide
  have hdescent : baseEnd_837171 < baseStart_837171 := by decide
  rcases family_descends (prefixWord ++ tailWord_837171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837178 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_837178 : Nat := 118140960795 + 837178 * 2 ^ 59
def prefixEnd_837178 : Nat := 4983230072969 + 3 ^ 40 * 837178 * 2
def baseEnd_837178 : Nat := 382110850995405129711017

theorem tailTrace_837178 : CollatzResearch.WordTrace tailWord_837178 prefixEnd_837178 382110850995405129711017 := by
  unfold tailWord_837178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633597540263639866100047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20356260107369706309600125 7633597540263639866100047)
  ·
    refine ⟨11450396310395459799150071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7633597540263639866100047 11450396310395459799150071)
    ·
      refine ⟨17175594465593189698725107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11450396310395459799150071 17175594465593189698725107)
      ·
        refine ⟨25763391698389784548087661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17175594465593189698725107 25763391698389784548087661)
        ·
          refine ⟨9661271886896169205532873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25763391698389784548087661 9661271886896169205532873)
          ·
            refine ⟨7245953915172126904149655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9661271886896169205532873 7245953915172126904149655)
            ·
              refine ⟨10868930872758190356224483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245953915172126904149655 10868930872758190356224483)
              ·
                refine ⟨16303396309137285534336725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10868930872758190356224483 16303396309137285534336725)
                ·
                  refine ⟨382110850995405129711017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16303396309137285534336725 382110850995405129711017)
                  ·
                    rfl

theorem cell20_837178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_837178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837178 prefixEnd_837178 := by exact prefixLift 837178
  have htrace : WordTrace (prefixWord ++ tailWord_837178) baseStart_837178 baseEnd_837178 := by
    simpa [prefixWord, tailWord_837178, baseEnd_837178] using wordTrace_append hprefix tailTrace_837178
  have hstable : (prefixWord ++ tailWord_837178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837178).length < 2 ^ (prefixWord ++ tailWord_837178).sum := by decide
  have hdescent : baseEnd_837178 < baseStart_837178 := by decide
  rcases family_descends (prefixWord ++ tailWord_837178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837212 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_837212 : Nat := 118140960795 + 837212 * 2 ^ 59
def prefixEnd_837212 : Nat := 4983230072969 + 3 ^ 40 * 837212 * 2
def baseEnd_837212 : Nat := 382126369521852122577545

theorem tailTrace_837212 : CollatzResearch.WordTrace tailWord_837212 prefixEnd_837212 382126369521852122577545 := by
  unfold tailWord_837212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15267815121465691635568945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20357086828620922180758593 15267815121465691635568945)
  ·
    refine ⟨11450861341099268726676709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15267815121465691635568945 11450861341099268726676709)
    ·
      refine ⟨2147036501456112886251883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11450861341099268726676709 2147036501456112886251883)
      ·
        refine ⟨3220554752184169329377825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147036501456112886251883 3220554752184169329377825)
        ·
          refine ⟨2415416064138126997033369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3220554752184169329377825 2415416064138126997033369)
          ·
            refine ⟨1811562048103595247775027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415416064138126997033369 1811562048103595247775027)
            ·
              refine ⟨2717343072155392871662541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811562048103595247775027 2717343072155392871662541)
              ·
                refine ⟨1019003652058272326873453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2717343072155392871662541 1019003652058272326873453)
                ·
                  refine ⟨382126369521852122577545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019003652058272326873453 382126369521852122577545)
                  ·
                    rfl

theorem cell20_837212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_837212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837212 prefixEnd_837212 := by exact prefixLift 837212
  have htrace : WordTrace (prefixWord ++ tailWord_837212) baseStart_837212 baseEnd_837212 := by
    simpa [prefixWord, tailWord_837212, baseEnd_837212] using wordTrace_append hprefix tailTrace_837212
  have hstable : (prefixWord ++ tailWord_837212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837212).length < 2 ^ (prefixWord ++ tailWord_837212).sum := by decide
  have hdescent : baseEnd_837212 < baseStart_837212 := by decide
  rcases family_descends (prefixWord ++ tailWord_837212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837271 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_837271 : Nat := 118140960795 + 837271 * 2 ^ 59
def prefixEnd_837271 : Nat := 4983230072969 + 3 ^ 40 * 837271 * 2
def baseEnd_837271 : Nat := 382153298729510139610637

theorem tailTrace_837271 : CollatzResearch.WordTrace tailWord_837271 prefixEnd_837271 382153298729510139610637 := by
  unfold tailWord_837271
  simp only [CollatzResearch.WordTrace]
  refine ⟨30537782149717636347535667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20358521433145090898357111 30537782149717636347535667)
  ·
    refine ⟨45806673224576454521303501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30537782149717636347535667 45806673224576454521303501)
    ·
      refine ⟨17177502459216170445488813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45806673224576454521303501 17177502459216170445488813)
      ·
        refine ⟨6441563422206063917058305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17177502459216170445488813 6441563422206063917058305)
        ·
          refine ⟨4831172566654547937793729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6441563422206063917058305 4831172566654547937793729)
          ·
            refine ⟨3623379424990910953345297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4831172566654547937793729 3623379424990910953345297)
            ·
              refine ⟨2717534568743183215008973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623379424990910953345297 2717534568743183215008973)
              ·
                refine ⟨1019075463278693705628365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2717534568743183215008973 1019075463278693705628365)
                ·
                  refine ⟨382153298729510139610637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019075463278693705628365 382153298729510139610637)
                  ·
                    rfl

theorem cell20_837271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_837271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837271 prefixEnd_837271 := by exact prefixLift 837271
  have htrace : WordTrace (prefixWord ++ tailWord_837271) baseStart_837271 baseEnd_837271 := by
    simpa [prefixWord, tailWord_837271, baseEnd_837271] using wordTrace_append hprefix tailTrace_837271
  have hstable : (prefixWord ++ tailWord_837271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837271).length < 2 ^ (prefixWord ++ tailWord_837271).sum := by decide
  have hdescent : baseEnd_837271 < baseStart_837271 := by decide
  rcases family_descends (prefixWord ++ tailWord_837271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837295 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 2]
def baseStart_837295 : Nat := 118140960795 + 837295 * 2 ^ 59
def prefixEnd_837295 : Nat := 4983230072969 + 3 ^ 40 * 837295 * 2
def baseEnd_837295 : Nat := 382164252983472722810539

theorem tailTrace_837295 : CollatzResearch.WordTrace tailWord_837295 prefixEnd_837295 382164252983472722810539 := by
  unfold tailWord_837295
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538657501630688446409339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20359105001087125630939559 30538657501630688446409339)
  ·
    refine ⟨45807986252446032669614009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30538657501630688446409339 45807986252446032669614009)
    ·
      refine ⟨34355989689334524502210507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45807986252446032669614009 34355989689334524502210507)
      ·
        refine ⟨51533984534001786753315761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34355989689334524502210507 51533984534001786753315761)
        ·
          refine ⟨38650488400501340064986821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51533984534001786753315761 38650488400501340064986821)
          ·
            refine ⟨7246966575094001262185029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38650488400501340064986821 7246966575094001262185029)
            ·
              refine ⟨1358806232830125236659693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7246966575094001262185029 1358806232830125236659693)
              ·
                refine ⟨509552337311296963747385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358806232830125236659693 509552337311296963747385)
                ·
                  refine ⟨382164252983472722810539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509552337311296963747385 382164252983472722810539)
                  ·
                    rfl

theorem cell20_837295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 2].length) (baseStart_837295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837295 prefixEnd_837295 := by exact prefixLift 837295
  have htrace : WordTrace (prefixWord ++ tailWord_837295) baseStart_837295 baseEnd_837295 := by
    simpa [prefixWord, tailWord_837295, baseEnd_837295] using wordTrace_append hprefix tailTrace_837295
  have hstable : (prefixWord ++ tailWord_837295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837295).length < 2 ^ (prefixWord ++ tailWord_837295).sum := by decide
  have hdescent : baseEnd_837295 < baseStart_837295 := by decide
  rcases family_descends (prefixWord ++ tailWord_837295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837299 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_837299 : Nat := 118140960795 + 837299 * 2 ^ 59
def prefixEnd_837299 : Nat := 4983230072969 + 3 ^ 40 * 837299 * 2
def baseEnd_837299 : Nat := 382166078692466486677189

theorem tailTrace_837299 : CollatzResearch.WordTrace tailWord_837299 prefixEnd_837299 382166078692466486677189 := by
  unfold tailWord_837299
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538803393616197129554951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20359202262410798086369967 30538803393616197129554951)
  ·
    refine ⟨45808205090424295694332427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30538803393616197129554951 45808205090424295694332427)
    ·
      refine ⟨68712307635636443541498641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45808205090424295694332427 68712307635636443541498641)
      ·
        refine ⟨51534230726727332656123981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68712307635636443541498641 51534230726727332656123981)
        ·
          refine ⟨19325336522522749746046493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51534230726727332656123981 19325336522522749746046493)
          ·
            refine ⟨7247001195946031154767435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19325336522522749746046493 7247001195946031154767435)
            ·
              refine ⟨10870501793919046732151153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247001195946031154767435 10870501793919046732151153)
              ·
                refine ⟨8152876345439285049113365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10870501793919046732151153 8152876345439285049113365)
                ·
                  refine ⟨382166078692466486677189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8152876345439285049113365 382166078692466486677189)
                  ·
                    rfl

theorem cell20_837299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_837299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837299 prefixEnd_837299 := by exact prefixLift 837299
  have htrace : WordTrace (prefixWord ++ tailWord_837299) baseStart_837299 baseEnd_837299 := by
    simpa [prefixWord, tailWord_837299, baseEnd_837299] using wordTrace_append hprefix tailTrace_837299
  have hstable : (prefixWord ++ tailWord_837299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837299).length < 2 ^ (prefixWord ++ tailWord_837299).sum := by decide
  have hdescent : baseEnd_837299 < baseStart_837299 := by decide
  rcases family_descends (prefixWord ++ tailWord_837299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837326 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_837326 : Nat := 118140960795 + 837326 * 2 ^ 59
def prefixEnd_837326 : Nat := 4983230072969 + 3 ^ 40 * 837326 * 2
def baseEnd_837326 : Nat := 382178402228174392777079

theorem tailTrace_837326 : CollatzResearch.WordTrace tailWord_837326 prefixEnd_837326 382178402228174392777079 := by
  unfold tailWord_837326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817473520564797592598479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20359858776345587160525221 3817473520564797592598479)
  ·
    refine ⟨5726210280847196388897719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817473520564797592598479 5726210280847196388897719)
    ·
      refine ⟨8589315421270794583346579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726210280847196388897719 8589315421270794583346579)
      ·
        refine ⟨12883973131906191875019869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8589315421270794583346579 12883973131906191875019869)
        ·
          refine ⟨4831489924464821953132451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12883973131906191875019869 4831489924464821953132451)
          ·
            refine ⟨7247234886697232929698677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831489924464821953132451 7247234886697232929698677)
            ·
              refine ⟨679428270627865587159251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7247234886697232929698677 679428270627865587159251)
              ·
                refine ⟨1019142405941798380738877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679428270627865587159251 1019142405941798380738877)
                ·
                  refine ⟨382178402228174392777079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019142405941798380738877 382178402228174392777079)
                  ·
                    rfl

theorem cell20_837326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_837326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837326 prefixEnd_837326 := by exact prefixLift 837326
  have htrace : WordTrace (prefixWord ++ tailWord_837326) baseStart_837326 baseEnd_837326 := by
    simpa [prefixWord, tailWord_837326, baseEnd_837326] using wordTrace_append hprefix tailTrace_837326
  have hstable : (prefixWord ++ tailWord_837326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837326).length < 2 ^ (prefixWord ++ tailWord_837326).sum := by decide
  have hdescent : baseEnd_837326 < baseStart_837326 := by decide
  rcases family_descends (prefixWord ++ tailWord_837326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837361 : List Nat := [1, 2, 2, 2, 2, 5, 6]
def baseStart_837361 : Nat := 118140960795 + 837361 * 2 ^ 59
def prefixEnd_837361 : Nat := 4983230072969 + 3 ^ 40 * 837361 * 2
def baseEnd_837361 : Nat := 42466041909096647401141

theorem tailTrace_837361 : CollatzResearch.WordTrace tailWord_837361 prefixEnd_837361 42466041909096647401141 := by
  unfold tailWord_837361
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541064719391581718311937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20360709812927721145541291 30541064719391581718311937)
  ·
    refine ⟨22905798539543686288733953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30541064719391581718311937 22905798539543686288733953)
    ·
      refine ⟨17179348904657764716550465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22905798539543686288733953 17179348904657764716550465)
      ·
        refine ⟨12884511678493323537412849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17179348904657764716550465 12884511678493323537412849)
        ·
          refine ⟨9663383758869992653059637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12884511678493323537412849 9663383758869992653059637)
          ·
            refine ⟨905942227394061811224341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9663383758869992653059637 905942227394061811224341)
            ·
              refine ⟨42466041909096647401141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 905942227394061811224341 42466041909096647401141)
              ·
                rfl

theorem cell20_837361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_837361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837361 prefixEnd_837361 := by exact prefixLift 837361
  have htrace : WordTrace (prefixWord ++ tailWord_837361) baseStart_837361 baseEnd_837361 := by
    simpa [prefixWord, tailWord_837361, baseEnd_837361] using wordTrace_append hprefix tailTrace_837361
  have hstable : (prefixWord ++ tailWord_837361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837361).length < 2 ^ (prefixWord ++ tailWord_837361).sum := by decide
  have hdescent : baseEnd_837361 < baseStart_837361 := by decide
  rcases family_descends (prefixWord ++ tailWord_837361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837378 : List Nat := [3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_837378 : Nat := 118140960795 + 837378 * 2 ^ 59
def prefixEnd_837378 : Nat := 4983230072969 + 3 ^ 40 * 837378 * 2
def baseEnd_837378 : Nat := 127400712148364441014511

theorem tailTrace_837378 : CollatzResearch.WordTrace tailWord_837378 prefixEnd_837378 127400712148364441014511 := by
  unfold tailWord_837378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7635421190082498405420197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20361123173553329081120525 7635421190082498405420197)
  ·
    refine ⟨1431641473140468451016287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7635421190082498405420197 1431641473140468451016287)
    ·
      refine ⟨2147462209710702676524431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431641473140468451016287 2147462209710702676524431)
      ·
        refine ⟨3221193314566054014786647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147462209710702676524431 3221193314566054014786647)
        ·
          refine ⟨4831789971849081022179971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221193314566054014786647 4831789971849081022179971)
          ·
            refine ⟨7247684957773621533269957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831789971849081022179971 7247684957773621533269957)
            ·
              refine ⟨1358940929582554037488117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7247684957773621533269957 1358940929582554037488117)
              ·
                refine ⟨127400712148364441014511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1358940929582554037488117 127400712148364441014511)
                ·
                  rfl

theorem cell20_837378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_837378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837378 prefixEnd_837378 := by exact prefixLift 837378
  have htrace : WordTrace (prefixWord ++ tailWord_837378) baseStart_837378 baseEnd_837378 := by
    simpa [prefixWord, tailWord_837378, baseEnd_837378] using wordTrace_append hprefix tailTrace_837378
  have hstable : (prefixWord ++ tailWord_837378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837378).length < 2 ^ (prefixWord ++ tailWord_837378).sum := by decide
  have hdescent : baseEnd_837378 < baseStart_837378 := by decide
  rcases family_descends (prefixWord ++ tailWord_837378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837399 : List Nat := [1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_837399 : Nat := 118140960795 + 837399 * 2 ^ 59
def prefixEnd_837399 : Nat := 4983230072969 + 3 ^ 40 * 837399 * 2
def baseEnd_837399 : Nat := 127403907139103527781149

theorem tailTrace_837399 : CollatzResearch.WordTrace tailWord_837399 prefixEnd_837399 127403907139103527781149 := by
  unfold tailWord_837399
  simp only [CollatzResearch.WordTrace]
  refine ⟨30542450693253914208195251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20361633795502609472130167 30542450693253914208195251)
  ·
    refine ⟨45813676039880871312292877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30542450693253914208195251 45813676039880871312292877)
    ·
      refine ⟨17180128514955326742109829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45813676039880871312292877 17180128514955326742109829)
      ·
        refine ⟨3221274096554123764145593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17180128514955326742109829 3221274096554123764145593)
        ·
          refine ⟨2415955572415592823109195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221274096554123764145593 2415955572415592823109195)
          ·
            refine ⟨3623933358623389234663793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415955572415592823109195 3623933358623389234663793)
            ·
              refine ⟨2717950018967541925997845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623933358623389234663793 2717950018967541925997845)
              ·
                refine ⟨127403907139103527781149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2717950018967541925997845 127403907139103527781149)
                ·
                  rfl

theorem cell20_837399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_837399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837399 prefixEnd_837399 := by exact prefixLift 837399
  have htrace : WordTrace (prefixWord ++ tailWord_837399) baseStart_837399 baseEnd_837399 := by
    simpa [prefixWord, tailWord_837399, baseEnd_837399] using wordTrace_append hprefix tailTrace_837399
  have hstable : (prefixWord ++ tailWord_837399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837399).length < 2 ^ (prefixWord ++ tailWord_837399).sum := by decide
  have hdescent : baseEnd_837399 < baseStart_837399 := by decide
  rcases family_descends (prefixWord ++ tailWord_837399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837420 : List Nat := [2, 2, 1, 1, 1, 13]
def baseStart_837420 : Nat := 118140960795 + 837420 * 2 ^ 59
def prefixEnd_837420 : Nat := 4983230072969 + 3 ^ 40 * 837420 * 2
def baseEnd_837420 : Nat := 14156344681093623838643

theorem tailTrace_837420 : CollatzResearch.WordTrace tailWord_837420 prefixEnd_837420 14156344681093623838643 := by
  unfold tailWord_837420
  simp only [CollatzResearch.WordTrace]
  refine ⟨15271608313088917397354857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20362144417451889863139809 15271608313088917397354857)
  ·
    refine ⟨11453706234816688048016143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15271608313088917397354857 11453706234816688048016143)
    ·
      refine ⟨17180559352225032072024215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11453706234816688048016143 17180559352225032072024215)
      ·
        refine ⟨25770839028337548108036323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17180559352225032072024215 25770839028337548108036323)
        ·
          refine ⟨38656258542506322162054485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25770839028337548108036323 38656258542506322162054485)
          ·
            refine ⟨14156344681093623838643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38656258542506322162054485 14156344681093623838643)
            ·
              rfl

theorem cell20_837420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 13].length) (baseStart_837420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837420 prefixEnd_837420 := by exact prefixLift 837420
  have htrace : WordTrace (prefixWord ++ tailWord_837420) baseStart_837420 baseEnd_837420 := by
    simpa [prefixWord, tailWord_837420, baseEnd_837420] using wordTrace_append hprefix tailTrace_837420
  have hstable : (prefixWord ++ tailWord_837420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837420).length < 2 ^ (prefixWord ++ tailWord_837420).sum := by decide
  have hdescent : baseEnd_837420 < baseStart_837420 := by decide
  rcases family_descends (prefixWord ++ tailWord_837420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837422 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_837422 : Nat := 118140960795 + 837422 * 2 ^ 59
def prefixEnd_837422 : Nat := 4983230072969 + 3 ^ 40 * 837422 * 2
def baseEnd_837422 : Nat := 382222219244024725576687

theorem tailTrace_837422 : CollatzResearch.WordTrace tailWord_837422 prefixEnd_837422 382222219244024725576687 := by
  unfold tailWord_837422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817911196521323642035315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20362193048113726090855013 3817911196521323642035315)
  ·
    refine ⟨5726866794781985463052973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817911196521323642035315 5726866794781985463052973)
    ·
      refine ⟨2147575048043244548644865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5726866794781985463052973 2147575048043244548644865)
      ·
        refine ⟨1610681286032433411483649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147575048043244548644865 1610681286032433411483649)
        ·
          refine ⟨1208010964524325058612737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610681286032433411483649 1208010964524325058612737)
          ·
            refine ⟨906008223393243793959553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208010964524325058612737 906008223393243793959553)
            ·
              refine ⟨679506167544932845469665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906008223393243793959553 679506167544932845469665)
              ·
                refine ⟨509629625658699634102249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679506167544932845469665 509629625658699634102249)
                ·
                  refine ⟨382222219244024725576687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509629625658699634102249 382222219244024725576687)
                  ·
                    rfl

theorem cell20_837422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_837422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837422 prefixEnd_837422 := by exact prefixLift 837422
  have htrace : WordTrace (prefixWord ++ tailWord_837422) baseStart_837422 baseEnd_837422 := by
    simpa [prefixWord, tailWord_837422, baseEnd_837422] using wordTrace_append hprefix tailTrace_837422
  have hstable : (prefixWord ++ tailWord_837422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837422).length < 2 ^ (prefixWord ++ tailWord_837422).sum := by decide
  have hdescent : baseEnd_837422 < baseStart_837422 := by decide
  rcases family_descends (prefixWord ++ tailWord_837422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837426 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_837426 : Nat := 118140960795 + 837426 * 2 ^ 59
def prefixEnd_837426 : Nat := 4983230072969 + 3 ^ 40 * 837426 * 2
def baseEnd_837426 : Nat := 382224044953018489443337

theorem tailTrace_837426 : CollatzResearch.WordTrace tailWord_837426 prefixEnd_837426 382224044953018489443337 := by
  unfold tailWord_837426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7635858866039024454857033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20362290309437398546285421 7635858866039024454857033)
  ·
    refine ⟨5726894149529268341142775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7635858866039024454857033 5726894149529268341142775)
    ·
      refine ⟨8590341224293902511714163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726894149529268341142775 8590341224293902511714163)
      ·
        refine ⟨12885511836440853767571245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8590341224293902511714163 12885511836440853767571245)
        ·
          refine ⟨4832066938665320162839217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12885511836440853767571245 4832066938665320162839217)
          ·
            refine ⟨3624050203998990122129413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4832066938665320162839217 3624050203998990122129413)
            ·
              refine ⟨679509413249810647899265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3624050203998990122129413 679509413249810647899265)
              ·
                refine ⟨509632059937357985924449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679509413249810647899265 509632059937357985924449)
                ·
                  refine ⟨382224044953018489443337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509632059937357985924449 382224044953018489443337)
                  ·
                    rfl

theorem cell20_837426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_837426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837426 prefixEnd_837426 := by exact prefixLift 837426
  have htrace : WordTrace (prefixWord ++ tailWord_837426) baseStart_837426 baseEnd_837426 := by
    simpa [prefixWord, tailWord_837426, baseEnd_837426] using wordTrace_append hprefix tailTrace_837426
  have hstable : (prefixWord ++ tailWord_837426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837426).length < 2 ^ (prefixWord ++ tailWord_837426).sum := by decide
  have hdescent : baseEnd_837426 < baseStart_837426 := by decide
  rcases family_descends (prefixWord ++ tailWord_837426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837433 : List Nat := [1, 2, 1, 7, 1, 2, 1, 5]
def baseStart_837433 : Nat := 118140960795 + 837433 * 2 ^ 59
def prefixEnd_837433 : Nat := 4983230072969 + 3 ^ 40 * 837433 * 2
def baseEnd_837433 : Nat := 127409079981252525403325

theorem tailTrace_837433 : CollatzResearch.WordTrace tailWord_837433 prefixEnd_837433 127409079981252525403325 := by
  unfold tailWord_837433
  simp only [CollatzResearch.WordTrace]
  refine ⟨30543690775130738014932953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20362460516753825343288635 30543690775130738014932953)
  ·
    refine ⟨22907768081348053511199715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30543690775130738014932953 22907768081348053511199715)
    ·
      refine ⟨34361652122022080266799573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22907768081348053511199715 34361652122022080266799573)
      ·
        refine ⟨805351221609892506253115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34361652122022080266799573 805351221609892506253115)
        ·
          refine ⟨1208026832414838759379673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805351221609892506253115 1208026832414838759379673)
          ·
            refine ⟨906020124311129069534755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208026832414838759379673 906020124311129069534755)
            ·
              refine ⟨1359030186466693604302133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906020124311129069534755 1359030186466693604302133)
              ·
                refine ⟨127409079981252525403325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1359030186466693604302133 127409079981252525403325)
                ·
                  rfl

theorem cell20_837433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_837433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837433 prefixEnd_837433 := by exact prefixLift 837433
  have htrace : WordTrace (prefixWord ++ tailWord_837433) baseStart_837433 baseEnd_837433 := by
    simpa [prefixWord, tailWord_837433, baseEnd_837433] using wordTrace_append hprefix tailTrace_837433
  have hstable : (prefixWord ++ tailWord_837433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837433).length < 2 ^ (prefixWord ++ tailWord_837433).sum := by decide
  have hdescent : baseEnd_837433 < baseStart_837433 := by decide
  rcases family_descends (prefixWord ++ tailWord_837433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837475 : List Nat := [1, 1, 1, 5, 4, 1, 7]
def baseStart_837475 : Nat := 118140960795 + 837475 * 2 ^ 59
def prefixEnd_837475 : Nat := 4983230072969 + 3 ^ 40 * 837475 * 2
def baseEnd_837475 : Nat := 42471823320910232978867

theorem tailTrace_837475 : CollatzResearch.WordTrace tailWord_837475 prefixEnd_837475 42471823320910232978867 := by
  unfold tailWord_837475
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545222640978579187961879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20363481760652386125307919 30545222640978579187961879)
  ·
    refine ⟨45817833961467868781942819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30545222640978579187961879 45817833961467868781942819)
    ·
      refine ⟨68726750942201803172914229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45817833961467868781942819 68726750942201803172914229)
      ·
        refine ⟨6443132900831419047460709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68726750942201803172914229 6443132900831419047460709)
        ·
          refine ⟨1208087418905891071398883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6443132900831419047460709 1208087418905891071398883)
          ·
            refine ⟨1812131128358836607098325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208087418905891071398883 1812131128358836607098325)
            ·
              refine ⟨42471823320910232978867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1812131128358836607098325 42471823320910232978867)
              ·
                rfl

theorem cell20_837475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_837475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837475 prefixEnd_837475 := by exact prefixLift 837475
  have htrace : WordTrace (prefixWord ++ tailWord_837475) baseStart_837475 baseEnd_837475 := by
    simpa [prefixWord, tailWord_837475, baseEnd_837475] using wordTrace_append hprefix tailTrace_837475
  have hstable : (prefixWord ++ tailWord_837475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837475).length < 2 ^ (prefixWord ++ tailWord_837475).sum := by decide
  have hdescent : baseEnd_837475 < baseStart_837475 := by decide
  rcases family_descends (prefixWord ++ tailWord_837475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837485 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 2]
def baseStart_837485 : Nat := 118140960795 + 837485 * 2 ^ 59
def prefixEnd_837485 : Nat := 4983230072969 + 3 ^ 40 * 837485 * 2
def baseEnd_837485 : Nat := 382250974160676506476429

theorem tailTrace_837485 : CollatzResearch.WordTrace tailWord_837485 prefixEnd_837485 382250974160676506476429 := by
  unfold tailWord_837485
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545587370942350895825909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20363724913961567263883939 30545587370942350895825909)
  ·
    refine ⟨2863648816025845396483679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30545587370942350895825909 2863648816025845396483679)
    ·
      refine ⟨4295473224038768094725519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863648816025845396483679 4295473224038768094725519)
      ·
        refine ⟨6443209836058152142088279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295473224038768094725519 6443209836058152142088279)
        ·
          refine ⟨9664814754087228213132419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443209836058152142088279 9664814754087228213132419)
          ·
            refine ⟨14497222131130842319698629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9664814754087228213132419 14497222131130842319698629)
            ·
              refine ⟨2718229149587032934943493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14497222131130842319698629 2718229149587032934943493)
              ·
                refine ⟨509667965547568675301905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2718229149587032934943493 509667965547568675301905)
                ·
                  refine ⟨382250974160676506476429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509667965547568675301905 382250974160676506476429)
                  ·
                    rfl

theorem cell20_837485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_837485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837485 prefixEnd_837485 := by exact prefixLift 837485
  have htrace : WordTrace (prefixWord ++ tailWord_837485) baseStart_837485 baseEnd_837485 := by
    simpa [prefixWord, tailWord_837485, baseEnd_837485] using wordTrace_append hprefix tailTrace_837485
  have hstable : (prefixWord ++ tailWord_837485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837485).length < 2 ^ (prefixWord ++ tailWord_837485).sum := by decide
  have hdescent : baseEnd_837485 < baseStart_837485 := by decide
  rcases family_descends (prefixWord ++ tailWord_837485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837526 : List Nat := [5, 3, 1, 1, 2, 2, 6]
def baseStart_837526 : Nat := 118140960795 + 837526 * 2 ^ 59
def prefixEnd_837526 : Nat := 4983230072969 + 3 ^ 40 * 837526 * 2
def baseEnd_837526 : Nat := 42474409741984731789955

theorem tailTrace_837526 : CollatzResearch.WordTrace tailWord_837526 prefixEnd_837526 42474409741984731789955 := by
  unfold tailWord_837526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909192672737113431129277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20364721842529209932045621 1909192672737113431129277)
  ·
    refine ⟨715947252276417536673479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1909192672737113431129277 715947252276417536673479)
    ·
      refine ⟨1073920878414626305010219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715947252276417536673479 1073920878414626305010219)
      ·
        refine ⟨1610881317621939457515329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073920878414626305010219 1610881317621939457515329)
        ·
          refine ⟨1208160988216454593136497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610881317621939457515329 1208160988216454593136497)
          ·
            refine ⟨906120741162340944852373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208160988216454593136497 906120741162340944852373)
            ·
              refine ⟨42474409741984731789955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 906120741162340944852373 42474409741984731789955)
              ·
                rfl

theorem cell20_837526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 6].length) (baseStart_837526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837526 prefixEnd_837526 := by exact prefixLift 837526
  have htrace : WordTrace (prefixWord ++ tailWord_837526) baseStart_837526 baseEnd_837526 := by
    simpa [prefixWord, tailWord_837526, baseEnd_837526] using wordTrace_append hprefix tailTrace_837526
  have hstable : (prefixWord ++ tailWord_837526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837526).length < 2 ^ (prefixWord ++ tailWord_837526).sum := by decide
  have hdescent : baseEnd_837526 < baseStart_837526 := by decide
  rcases family_descends (prefixWord ++ tailWord_837526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837540 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 2]
def baseStart_837540 : Nat := 118140960795 + 837540 * 2 ^ 59
def prefixEnd_837540 : Nat := 4983230072969 + 3 ^ 40 * 837540 * 2
def baseEnd_837540 : Nat := 382276077659340759642871

theorem tailTrace_837540 : CollatzResearch.WordTrace tailWord_837540 prefixEnd_837540 382276077659340759642871 := by
  unfold tailWord_837540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15273796692871547644539037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20365062257162063526052049 15273796692871547644539037)
  ·
    refine ⟨5727673759826830366702139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15273796692871547644539037 5727673759826830366702139)
    ·
      refine ⟨8591510639740245550053209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727673759826830366702139 8591510639740245550053209)
      ·
        refine ⟨6443632979805184162539907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8591510639740245550053209 6443632979805184162539907)
        ·
          refine ⟨9665449469707776243809861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443632979805184162539907 9665449469707776243809861)
          ·
            refine ⟨1812271775570208045714349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9665449469707776243809861 1812271775570208045714349)
            ·
              refine ⟨679601915838828017142881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1812271775570208045714349 679601915838828017142881)
              ·
                refine ⟨509701436879121012857161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679601915838828017142881 509701436879121012857161)
                ·
                  refine ⟨382276077659340759642871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509701436879121012857161 382276077659340759642871)
                  ·
                    rfl

theorem cell20_837540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_837540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837540 prefixEnd_837540 := by exact prefixLift 837540
  have htrace : WordTrace (prefixWord ++ tailWord_837540) baseStart_837540 baseEnd_837540 := by
    simpa [prefixWord, tailWord_837540, baseEnd_837540] using wordTrace_append hprefix tailTrace_837540
  have hstable : (prefixWord ++ tailWord_837540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837540).length < 2 ^ (prefixWord ++ tailWord_837540).sum := by decide
  have hdescent : baseEnd_837540 < baseStart_837540 := by decide
  rcases family_descends (prefixWord ++ tailWord_837540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837550 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_837550 : Nat := 118140960795 + 837550 * 2 ^ 59
def prefixEnd_837550 : Nat := 4983230072969 + 3 ^ 40 * 837550 * 2
def baseEnd_837550 : Nat := 382280641931825169309497

theorem tailTrace_837550 : CollatzResearch.WordTrace tailWord_837550 prefixEnd_837550 382280641931825169309497 := by
  unfold tailWord_837550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818494764463358374617763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20365305410471244664628069 3818494764463358374617763)
  ·
    refine ⟨5727742146695037561926645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818494764463358374617763 5727742146695037561926645)
    ·
      refine ⟨536975826252659771430623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5727742146695037561926645 536975826252659771430623)
      ·
        refine ⟨805463739378989657145935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536975826252659771430623 805463739378989657145935)
        ·
          refine ⟨1208195609068484485718903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805463739378989657145935 1208195609068484485718903)
          ·
            refine ⟨1812293413602726728578355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208195609068484485718903 1812293413602726728578355)
            ·
              refine ⟨2718440120404090092867533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812293413602726728578355 2718440120404090092867533)
              ·
                refine ⟨1019415045151533784825325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718440120404090092867533 1019415045151533784825325)
                ·
                  refine ⟨382280641931825169309497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019415045151533784825325 382280641931825169309497)
                  ·
                    rfl

theorem cell20_837550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_837550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837550 prefixEnd_837550 := by exact prefixLift 837550
  have htrace : WordTrace (prefixWord ++ tailWord_837550) baseStart_837550 baseEnd_837550 := by
    simpa [prefixWord, tailWord_837550, baseEnd_837550] using wordTrace_append hprefix tailTrace_837550
  have hstable : (prefixWord ++ tailWord_837550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837550).length < 2 ^ (prefixWord ++ tailWord_837550).sum := by decide
  have hdescent : baseEnd_837550 < baseStart_837550 := by decide
  rcases family_descends (prefixWord ++ tailWord_837550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837599 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 2]
def baseStart_837599 : Nat := 118140960795 + 837599 * 2 ^ 59
def prefixEnd_837599 : Nat := 4983230072969 + 3 ^ 40 * 837599 * 2
def baseEnd_837599 : Nat := 382303006866998776675963

theorem tailTrace_837599 : CollatzResearch.WordTrace tailWord_837599 prefixEnd_837599 382303006866998776675963 := by
  unfold tailWord_837599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30549745292529348365475851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20366496861686232243650567 30549745292529348365475851)
  ·
    refine ⟨45824617938794022548213777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30549745292529348365475851 45824617938794022548213777)
    ·
      refine ⟨34368463454095516911160333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45824617938794022548213777 34368463454095516911160333)
      ·
        refine ⟨12888173795285818841685125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34368463454095516911160333 12888173795285818841685125)
        ·
          refine ⟨2416532586616091032815961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12888173795285818841685125 2416532586616091032815961)
          ·
            refine ⟨1812399439962068274611971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2416532586616091032815961 1812399439962068274611971)
            ·
              refine ⟨2718599159943102411917957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812399439962068274611971 2718599159943102411917957)
              ·
                refine ⟨509737342489331702234617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2718599159943102411917957 509737342489331702234617)
                ·
                  refine ⟨382303006866998776675963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509737342489331702234617 382303006866998776675963)
                  ·
                    rfl

theorem cell20_837599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 2].length) (baseStart_837599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837599 prefixEnd_837599 := by exact prefixLift 837599
  have htrace : WordTrace (prefixWord ++ tailWord_837599) baseStart_837599 baseEnd_837599 := by
    simpa [prefixWord, tailWord_837599, baseEnd_837599] using wordTrace_append hprefix tailTrace_837599
  have hstable : (prefixWord ++ tailWord_837599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837599).length < 2 ^ (prefixWord ++ tailWord_837599).sum := by decide
  have hdescent : baseEnd_837599 < baseStart_837599 := by decide
  rcases family_descends (prefixWord ++ tailWord_837599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837602 : List Nat := [3, 3, 3, 1, 3, 1, 1, 5]
def baseStart_837602 : Nat := 118140960795 + 837602 * 2 ^ 59
def prefixEnd_837602 : Nat := 4983230072969 + 3 ^ 40 * 837602 * 2
def baseEnd_837602 : Nat := 127434792049581366525317

theorem tailTrace_837602 : CollatzResearch.WordTrace tailWord_837602 prefixEnd_837602 127434792049581366525317 := by
  unfold tailWord_837602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637463677879619969458765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20366569807678986585223373 7637463677879619969458765)
  ·
    refine ⟨2864048879204857488547037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7637463677879619969458765 2864048879204857488547037)
    ·
      refine ⟨1074018329701821558205139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2864048879204857488547037 1074018329701821558205139)
      ·
        refine ⟨1611027494552732337307709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074018329701821558205139 1611027494552732337307709)
        ·
          refine ⟨604135310457274626490391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1611027494552732337307709 604135310457274626490391)
          ·
            refine ⟨906202965685911939735587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604135310457274626490391 906202965685911939735587)
            ·
              refine ⟨1359304448528867909603381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906202965685911939735587 1359304448528867909603381)
              ·
                refine ⟨127434792049581366525317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1359304448528867909603381 127434792049581366525317)
                ·
                  rfl

theorem cell20_837602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_837602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837602 prefixEnd_837602 := by exact prefixLift 837602
  have htrace : WordTrace (prefixWord ++ tailWord_837602) baseStart_837602 baseEnd_837602 := by
    simpa [prefixWord, tailWord_837602, baseEnd_837602] using wordTrace_append hprefix tailTrace_837602
  have hstable : (prefixWord ++ tailWord_837602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837602).length < 2 ^ (prefixWord ++ tailWord_837602).sum := by decide
  have hdescent : baseEnd_837602 < baseStart_837602 := by decide
  rcases family_descends (prefixWord ++ tailWord_837602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837637 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 2]
def baseStart_837637 : Nat := 118140960795 + 837637 * 2 ^ 59
def prefixEnd_837637 : Nat := 4983230072969 + 3 ^ 40 * 837637 * 2
def baseEnd_837637 : Nat := 382320351102439533409141

theorem tailTrace_837637 : CollatzResearch.WordTrace tailWord_837637 prefixEnd_837637 382320351102439533409141 := by
  unfold tailWord_837637
  simp only [CollatzResearch.WordTrace]
  refine ⟨30551131266391680855359165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20367420844261120570239443 30551131266391680855359165)
  ·
    refine ⟨11456674224896880320759687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30551131266391680855359165 11456674224896880320759687)
    ·
      refine ⟨17185011337345320481139531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11456674224896880320759687 17185011337345320481139531)
      ·
        refine ⟨25777517006017980721709297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17185011337345320481139531 25777517006017980721709297)
        ·
          refine ⟨19333137754513485541281973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25777517006017980721709297 19333137754513485541281973)
          ·
            refine ⟨1812481664485639269495185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19333137754513485541281973 1812481664485639269495185)
            ·
              refine ⟨1359361248364229452121389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812481664485639269495185 1359361248364229452121389)
              ·
                refine ⟨509760468136586044545521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359361248364229452121389 509760468136586044545521)
                ·
                  refine ⟨382320351102439533409141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509760468136586044545521 382320351102439533409141)
                  ·
                    rfl

theorem cell20_837637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_837637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837637 prefixEnd_837637 := by exact prefixLift 837637
  have htrace : WordTrace (prefixWord ++ tailWord_837637) baseStart_837637 baseEnd_837637 := by
    simpa [prefixWord, tailWord_837637, baseEnd_837637] using wordTrace_append hprefix tailTrace_837637
  have hstable : (prefixWord ++ tailWord_837637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837637).length < 2 ^ (prefixWord ++ tailWord_837637).sum := by decide
  have hdescent : baseEnd_837637 < baseStart_837637 := by decide
  rcases family_descends (prefixWord ++ tailWord_837637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837658 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_837658 : Nat := 118140960795 + 837658 * 2 ^ 59
def prefixEnd_837658 : Nat := 4983230072969 + 3 ^ 40 * 837658 * 2
def baseEnd_837658 : Nat := 382329936074656793709055

theorem tailTrace_837658 : CollatzResearch.WordTrace tailWord_837658 prefixEnd_837658 382329936074656793709055 := by
  unfold tailWord_837658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637974299828900360468407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20367931466210400961249085 7637974299828900360468407)
  ·
    refine ⟨11456961449743350540702611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7637974299828900360468407 11456961449743350540702611)
    ·
      refine ⟨17185442174615025811053917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11456961449743350540702611 17185442174615025811053917)
      ·
        refine ⟨6444540815480634679145219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17185442174615025811053917 6444540815480634679145219)
        ·
          refine ⟨9666811223220952018717829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444540815480634679145219 9666811223220952018717829)
          ·
            refine ⟨1812527104353928503509593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9666811223220952018717829 1812527104353928503509593)
            ·
              refine ⟨1359395328265446377632195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812527104353928503509593 1359395328265446377632195)
              ·
                refine ⟨2039092992398169566448293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359395328265446377632195 2039092992398169566448293)
                ·
                  refine ⟨382329936074656793709055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039092992398169566448293 382329936074656793709055)
                  ·
                    rfl

theorem cell20_837658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_837658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837658 prefixEnd_837658 := by exact prefixLift 837658
  have htrace : WordTrace (prefixWord ++ tailWord_837658) baseStart_837658 baseEnd_837658 := by
    simpa [prefixWord, tailWord_837658, baseEnd_837658] using wordTrace_append hprefix tailTrace_837658
  have hstable : (prefixWord ++ tailWord_837658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837658).length < 2 ^ (prefixWord ++ tailWord_837658).sum := by decide
  have hdescent : baseEnd_837658 < baseStart_837658 := by decide
  rcases family_descends (prefixWord ++ tailWord_837658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837682 : List Nat := [3, 2, 1, 1, 2, 5, 2, 4]
def baseStart_837682 : Nat := 118140960795 + 837682 * 2 ^ 59
def prefixEnd_837682 : Nat := 4983230072969 + 3 ^ 40 * 837682 * 2
def baseEnd_837682 : Nat := 127446963442873125636319

theorem tailTrace_837682 : CollatzResearch.WordTrace tailWord_837682 prefixEnd_837682 127446963442873125636319 := by
  unfold tailWord_837682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638193137807163385186825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20368515034152435693831533 7638193137807163385186825)
  ·
    refine ⟨5728644853355372538890119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7638193137807163385186825 5728644853355372538890119)
    ·
      refine ⟨8592967280033058808335179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5728644853355372538890119 8592967280033058808335179)
      ·
        refine ⟨12889450920049588212502769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8592967280033058808335179 12889450920049588212502769)
        ·
          refine ⟨9667088190037191159377077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12889450920049588212502769 9667088190037191159377077)
          ·
            refine ⟨906289517815986671191601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9667088190037191159377077 906289517815986671191601)
            ·
              refine ⟨679717138361990003393701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906289517815986671191601 679717138361990003393701)
              ·
                refine ⟨127446963442873125636319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679717138361990003393701 127446963442873125636319)
                ·
                  rfl

theorem cell20_837682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_837682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837682 prefixEnd_837682 := by exact prefixLift 837682
  have htrace : WordTrace (prefixWord ++ tailWord_837682) baseStart_837682 baseEnd_837682 := by
    simpa [prefixWord, tailWord_837682, baseEnd_837682] using wordTrace_append hprefix tailTrace_837682
  have hstable : (prefixWord ++ tailWord_837682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837682).length < 2 ^ (prefixWord ++ tailWord_837682).sum := by decide
  have hdescent : baseEnd_837682 < baseStart_837682 := by decide
  rcases family_descends (prefixWord ++ tailWord_837682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837710 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_837710 : Nat := 118140960795 + 837710 * 2 ^ 59
def prefixEnd_837710 : Nat := 4983230072969 + 3 ^ 40 * 837710 * 2
def baseEnd_837710 : Nat := 382353670291575723975509

theorem tailTrace_837710 : CollatzResearch.WordTrace tailWord_837710 prefixEnd_837710 382353670291575723975509 := by
  unfold tailWord_837710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3819224224390901790345823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20369195863418142881844389 3819224224390901790345823)
  ·
    refine ⟨5728836336586352685518735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3819224224390901790345823 5728836336586352685518735)
    ·
      refine ⟨8593254504879529028278103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5728836336586352685518735 8593254504879529028278103)
      ·
        refine ⟨12889881757319293542417155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593254504879529028278103 12889881757319293542417155)
        ·
          refine ⟨19334822635978940313625733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889881757319293542417155 19334822635978940313625733)
          ·
            refine ⟨3625279244246051308804825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19334822635978940313625733 3625279244246051308804825)
            ·
              refine ⟨2718959433184538481603619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625279244246051308804825 2718959433184538481603619)
              ·
                refine ⟨4078439149776807722405429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718959433184538481603619 4078439149776807722405429)
                ·
                  refine ⟨382353670291575723975509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078439149776807722405429 382353670291575723975509)
                  ·
                    rfl

theorem cell20_837710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_837710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837710 prefixEnd_837710 := by exact prefixLift 837710
  have htrace : WordTrace (prefixWord ++ tailWord_837710) baseStart_837710 baseEnd_837710 := by
    simpa [prefixWord, tailWord_837710, baseEnd_837710] using wordTrace_append hprefix tailTrace_837710
  have hstable : (prefixWord ++ tailWord_837710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837710).length < 2 ^ (prefixWord ++ tailWord_837710).sum := by decide
  have hdescent : baseEnd_837710 < baseStart_837710 := by decide
  rcases family_descends (prefixWord ++ tailWord_837710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837762 : List Nat := [3, 4, 13]
def baseStart_837762 : Nat := 118140960795 + 837762 * 2 ^ 59
def prefixEnd_837762 : Nat := 4983230072969 + 3 ^ 40 * 837762 * 2
def baseEnd_837762 : Nat := 524523188626192941347

theorem tailTrace_837762 : CollatzResearch.WordTrace tailWord_837762 prefixEnd_837762 524523188626192941347 := by
  unfold tailWord_837762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638922597734706800914885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20370460260625884802439693 7638922597734706800914885)
  ·
    refine ⟨1432297987075257525171541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7638922597734706800914885 1432297987075257525171541)
    ·
      refine ⟨524523188626192941347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 1432297987075257525171541 524523188626192941347)
      ·
        rfl

theorem cell20_837762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 13].length) (baseStart_837762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837762 prefixEnd_837762 := by exact prefixLift 837762
  have htrace : WordTrace (prefixWord ++ tailWord_837762) baseStart_837762 baseEnd_837762 := by
    simpa [prefixWord, tailWord_837762, baseEnd_837762] using wordTrace_append hprefix tailTrace_837762
  have hstable : (prefixWord ++ tailWord_837762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837762).length < 2 ^ (prefixWord ++ tailWord_837762).sum := by decide
  have hdescent : baseEnd_837762 < baseStart_837762 := by decide
  rcases family_descends (prefixWord ++ tailWord_837762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837765 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_837765 : Nat := 118140960795 + 837765 * 2 ^ 59
def prefixEnd_837765 : Nat := 4983230072969 + 3 ^ 40 * 837765 * 2
def baseEnd_837765 : Nat := 382378773790239977141951

theorem tailTrace_837765 : CollatzResearch.WordTrace tailWord_837765 prefixEnd_837765 382378773790239977141951 := by
  unfold tailWord_837765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555799809927958716018749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20370533206618639144012499 30555799809927958716018749)
  ·
    refine ⟨11458424928722984518507031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30555799809927958716018749 11458424928722984518507031)
    ·
      refine ⟨17187637393084476777760547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11458424928722984518507031 17187637393084476777760547)
      ·
        refine ⟨25781456089626715166640821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17187637393084476777760547 25781456089626715166640821)
        ·
          refine ⟨2417011508402504546872577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25781456089626715166640821 2417011508402504546872577)
          ·
            refine ⟨1812758631301878410154433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417011508402504546872577 1812758631301878410154433)
            ·
              refine ⟨1359568973476408807615825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812758631301878410154433 1359568973476408807615825)
              ·
                refine ⟨1019676730107306605711869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359568973476408807615825 1019676730107306605711869)
                ·
                  refine ⟨382378773790239977141951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019676730107306605711869 382378773790239977141951)
                  ·
                    rfl

theorem cell20_837765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_837765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837765 prefixEnd_837765 := by exact prefixLift 837765
  have htrace : WordTrace (prefixWord ++ tailWord_837765) baseStart_837765 baseEnd_837765 := by
    simpa [prefixWord, tailWord_837765, baseEnd_837765] using wordTrace_append hprefix tailTrace_837765
  have hstable : (prefixWord ++ tailWord_837765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837765).length < 2 ^ (prefixWord ++ tailWord_837765).sum := by decide
  have hdescent : baseEnd_837765 < baseStart_837765 := by decide
  rcases family_descends (prefixWord ++ tailWord_837765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837768 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 2]
def baseStart_837768 : Nat := 118140960795 + 837768 * 2 ^ 59
def prefixEnd_837768 : Nat := 4983230072969 + 3 ^ 40 * 837768 * 2
def baseEnd_837768 : Nat := 382380143071985300041939

theorem tailTrace_837768 : CollatzResearch.WordTrace tailWord_837768 prefixEnd_837768 382380143071985300041939 := by
  unfold tailWord_837768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15277954614458545114188979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20370606152611393485585305 15277954614458545114188979)
  ·
    refine ⟨22916931921687817671283469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15277954614458545114188979 22916931921687817671283469)
    ·
      refine ⟨8593849470632931626731301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22916931921687817671283469 8593849470632931626731301)
      ·
        refine ⟨1611346775743674680012119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8593849470632931626731301 1611346775743674680012119)
        ·
          refine ⟨2417020163615512020018179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611346775743674680012119 2417020163615512020018179)
          ·
            refine ⟨3625530245423268030027269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417020163615512020018179 3625530245423268030027269)
            ·
              refine ⟨679786921016862755630113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3625530245423268030027269 679786921016862755630113)
              ·
                refine ⟨509840190762647066722585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679786921016862755630113 509840190762647066722585)
                ·
                  refine ⟨382380143071985300041939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509840190762647066722585 382380143071985300041939)
                  ·
                    rfl

theorem cell20_837768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_837768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837768 prefixEnd_837768 := by exact prefixLift 837768
  have htrace : WordTrace (prefixWord ++ tailWord_837768) baseStart_837768 baseEnd_837768 := by
    simpa [prefixWord, tailWord_837768, baseEnd_837768] using wordTrace_append hprefix tailTrace_837768
  have hstable : (prefixWord ++ tailWord_837768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837768).length < 2 ^ (prefixWord ++ tailWord_837768).sum := by decide
  have hdescent : baseEnd_837768 < baseStart_837768 := by decide
  rcases family_descends (prefixWord ++ tailWord_837768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837793 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_837793 : Nat := 118140960795 + 837793 * 2 ^ 59
def prefixEnd_837793 : Nat := 4983230072969 + 3 ^ 40 * 837793 * 2
def baseEnd_837793 : Nat := 382391553753196324208503

theorem tailTrace_837793 : CollatzResearch.WordTrace tailWord_837793 prefixEnd_837793 382391553753196324208503 := by
  unfold tailWord_837793
  simp only [CollatzResearch.WordTrace]
  refine ⟨30556821053826519498038033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20371214035884346332025355 30556821053826519498038033)
  ·
    refine ⟨22917615790369889623528525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30556821053826519498038033 22917615790369889623528525)
    ·
      refine ⟨8594105921388708608823197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22917615790369889623528525 8594105921388708608823197)
      ·
        refine ⟨3222789720520765728308699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8594105921388708608823197 3222789720520765728308699)
        ·
          refine ⟨4834184580781148592463049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222789720520765728308699 4834184580781148592463049)
          ·
            refine ⟨3625638435585861444347287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4834184580781148592463049 3625638435585861444347287)
            ·
              refine ⟨5438457653378792166520931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625638435585861444347287 5438457653378792166520931)
              ·
                refine ⟨8157686480068188249781397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438457653378792166520931 8157686480068188249781397)
                ·
                  refine ⟨382391553753196324208503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8157686480068188249781397 382391553753196324208503)
                  ·
                    rfl

theorem cell20_837793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_837793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837793 prefixEnd_837793 := by exact prefixLift 837793
  have htrace : WordTrace (prefixWord ++ tailWord_837793) baseStart_837793 baseEnd_837793 := by
    simpa [prefixWord, tailWord_837793, baseEnd_837793] using wordTrace_append hprefix tailTrace_837793
  have hstable : (prefixWord ++ tailWord_837793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837793).length < 2 ^ (prefixWord ++ tailWord_837793).sum := by decide
  have hdescent : baseEnd_837793 < baseStart_837793 := by decide
  rcases family_descends (prefixWord ++ tailWord_837793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837796 : List Nat := [2, 3, 1, 2, 4, 1, 3, 4]
def baseStart_837796 : Nat := 118140960795 + 837796 * 2 ^ 59
def prefixEnd_837796 : Nat := 4983230072969 + 3 ^ 40 * 837796 * 2
def baseEnd_837796 : Nat := 127464307678313882369497

theorem tailTrace_837796 : CollatzResearch.WordTrace tailWord_837796 prefixEnd_837796 127464307678313882369497 := by
  unfold tailWord_837796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278465236407825505198621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20371286981877100673598161 15278465236407825505198621)
  ·
    refine ⟨5729424463652934564449483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15278465236407825505198621 5729424463652934564449483)
    ·
      refine ⟨8594136695479401846674225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5729424463652934564449483 8594136695479401846674225)
      ·
        refine ⟨6445602521609551385005669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8594136695479401846674225 6445602521609551385005669)
        ·
          refine ⟨1208550472801790884688563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6445602521609551385005669 1208550472801790884688563)
          ·
            refine ⟨1812825709202686327032845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208550472801790884688563 1812825709202686327032845)
            ·
              refine ⟨679809640951007372637317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1812825709202686327032845 679809640951007372637317)
              ·
                refine ⟨127464307678313882369497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679809640951007372637317 127464307678313882369497)
                ·
                  rfl

theorem cell20_837796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_837796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837796 prefixEnd_837796 := by exact prefixLift 837796
  have htrace : WordTrace (prefixWord ++ tailWord_837796) baseStart_837796 baseEnd_837796 := by
    simpa [prefixWord, tailWord_837796, baseEnd_837796] using wordTrace_append hprefix tailTrace_837796
  have hstable : (prefixWord ++ tailWord_837796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837796).length < 2 ^ (prefixWord ++ tailWord_837796).sum := by decide
  have hdescent : baseEnd_837796 < baseStart_837796 := by decide
  rcases family_descends (prefixWord ++ tailWord_837796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837807 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_837807 : Nat := 118140960795 + 837807 * 2 ^ 59
def prefixEnd_837807 : Nat := 4983230072969 + 3 ^ 40 * 837807 * 2
def baseEnd_837807 : Nat := 382397943734674497741779

theorem tailTrace_837807 : CollatzResearch.WordTrace tailWord_837807 prefixEnd_837807 382397943734674497741779 := by
  unfold tailWord_837807
  simp only [CollatzResearch.WordTrace]
  refine ⟨30557331675775799889047675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20371554450517199926031783 30557331675775799889047675)
  ·
    refine ⟨45835997513663699833571513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30557331675775799889047675 45835997513663699833571513)
    ·
      refine ⟨34376998135247774875178635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45835997513663699833571513 34376998135247774875178635)
      ·
        refine ⟨51565497202871662312767953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34376998135247774875178635 51565497202871662312767953)
        ·
          refine ⟨38674122902153746734575965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51565497202871662312767953 38674122902153746734575965)
          ·
            refine ⟨14502796088307655025465987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38674122902153746734575965 14502796088307655025465987)
            ·
              refine ⟨21754194132461482538198981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14502796088307655025465987 21754194132461482538198981)
              ·
                refine ⟨4078911399836527975912309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21754194132461482538198981 4078911399836527975912309)
                ·
                  refine ⟨382397943734674497741779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078911399836527975912309 382397943734674497741779)
                  ·
                    rfl

theorem cell20_837807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_837807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837807 prefixEnd_837807 := by exact prefixLift 837807
  have htrace : WordTrace (prefixWord ++ tailWord_837807) baseStart_837807 baseEnd_837807 := by
    simpa [prefixWord, tailWord_837807, baseEnd_837807] using wordTrace_append hprefix tailTrace_837807
  have hstable : (prefixWord ++ tailWord_837807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837807).length < 2 ^ (prefixWord ++ tailWord_837807).sum := by decide
  have hdescent : baseEnd_837807 < baseStart_837807 := by decide
  rcases family_descends (prefixWord ++ tailWord_837807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837820 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_837820 : Nat := 118140960795 + 837820 * 2 ^ 59
def prefixEnd_837820 : Nat := 4983230072969 + 3 ^ 40 * 837820 * 2
def baseEnd_837820 : Nat := 382403877288904230308393

theorem tailTrace_837820 : CollatzResearch.WordTrace tailWord_837820 prefixEnd_837820 382403877288904230308393 := by
  unfold tailWord_837820
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278902912364351554635457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20371870549819135406180609 15278902912364351554635457)
  ·
    refine ⟨11459177184273263665976593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15278902912364351554635457 11459177184273263665976593)
    ·
      refine ⟨8594382888204947749482445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11459177184273263665976593 8594382888204947749482445)
      ·
        refine ⟨3222893583076855406055917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8594382888204947749482445 3222893583076855406055917)
        ·
          refine ⟨1208585093653820777270969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3222893583076855406055917 1208585093653820777270969)
          ·
            refine ⟨906438820240365582953227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208585093653820777270969 906438820240365582953227)
            ·
              refine ⟨1359658230360548374429841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906438820240365582953227 1359658230360548374429841)
              ·
                refine ⟨1019743672770411280822381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359658230360548374429841 1019743672770411280822381)
                ·
                  refine ⟨382403877288904230308393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019743672770411280822381 382403877288904230308393)
                  ·
                    rfl

theorem cell20_837820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_837820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837820 prefixEnd_837820 := by exact prefixLift 837820
  have htrace : WordTrace (prefixWord ++ tailWord_837820) baseStart_837820 baseEnd_837820 := by
    simpa [prefixWord, tailWord_837820, baseEnd_837820] using wordTrace_append hprefix tailTrace_837820
  have hstable : (prefixWord ++ tailWord_837820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837820).length < 2 ^ (prefixWord ++ tailWord_837820).sum := by decide
  have hdescent : baseEnd_837820 < baseStart_837820 := by decide
  rcases family_descends (prefixWord ++ tailWord_837820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837824 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_837824 : Nat := 118140960795 + 837824 * 2 ^ 59
def prefixEnd_837824 : Nat := 4983230072969 + 3 ^ 40 * 837824 * 2
def baseEnd_837824 : Nat := 382405702997897994175043

theorem tailTrace_837824 : CollatzResearch.WordTrace tailWord_837824 prefixEnd_837824 382405702997897994175043 := by
  unfold tailWord_837824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278975858357105896208263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20371967811142807861611017 15278975858357105896208263)
  ·
    refine ⟨22918463787535658844312395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15278975858357105896208263 22918463787535658844312395)
    ·
      refine ⟨34377695681303488266468593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22918463787535658844312395 34377695681303488266468593)
      ·
        refine ⟨25783271760977616199851445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34377695681303488266468593 25783271760977616199851445)
        ·
          refine ⟨2417181727591651518736073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25783271760977616199851445 2417181727591651518736073)
          ·
            refine ⟨1812886295693738639052055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417181727591651518736073 1812886295693738639052055)
            ·
              refine ⟨2719329443540607958578083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812886295693738639052055 2719329443540607958578083)
              ·
                refine ⟨4078994165310911937867125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719329443540607958578083 4078994165310911937867125)
                ·
                  refine ⟨382405702997897994175043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078994165310911937867125 382405702997897994175043)
                  ·
                    rfl

theorem cell20_837824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_837824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837824 prefixEnd_837824 := by exact prefixLift 837824
  have htrace : WordTrace (prefixWord ++ tailWord_837824) baseStart_837824 baseEnd_837824 := by
    simpa [prefixWord, tailWord_837824, baseEnd_837824] using wordTrace_append hprefix tailTrace_837824
  have hstable : (prefixWord ++ tailWord_837824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837824).length < 2 ^ (prefixWord ++ tailWord_837824).sum := by decide
  have hdescent : baseEnd_837824 < baseStart_837824 := by decide
  rcases family_descends (prefixWord ++ tailWord_837824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837896 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_837896 : Nat := 118140960795 + 837896 * 2 ^ 59
def prefixEnd_837896 : Nat := 4983230072969 + 3 ^ 40 * 837896 * 2
def baseEnd_837896 : Nat := 382438565759785743774749

theorem tailTrace_837896 : CollatzResearch.WordTrace tailWord_837896 prefixEnd_837896 382438565759785743774749 := by
  unfold tailWord_837896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280288886226684044518771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20373718514968912059358361 15280288886226684044518771)
  ·
    refine ⟨22920433329340026066778157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15280288886226684044518771 22920433329340026066778157)
    ·
      refine ⟨8595162498502509775041809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22920433329340026066778157 8595162498502509775041809)
      ·
        refine ⟨6446371873876882331281357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8595162498502509775041809 6446371873876882331281357)
        ·
          refine ⟨2417389452703830874230509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6446371873876882331281357 2417389452703830874230509)
          ·
            refine ⟨906521044763936577836441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2417389452703830874230509 906521044763936577836441)
            ·
              refine ⟨679890783572952433377331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906521044763936577836441 679890783572952433377331)
              ·
                refine ⟨1019836175359428650065997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679890783572952433377331 1019836175359428650065997)
                ·
                  refine ⟨382438565759785743774749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019836175359428650065997 382438565759785743774749)
                  ·
                    rfl

theorem cell20_837896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_837896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837896 prefixEnd_837896 := by exact prefixLift 837896
  have htrace : WordTrace (prefixWord ++ tailWord_837896) baseStart_837896 baseEnd_837896 := by
    simpa [prefixWord, tailWord_837896, baseEnd_837896] using wordTrace_append hprefix tailTrace_837896
  have hstable : (prefixWord ++ tailWord_837896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837896).length < 2 ^ (prefixWord ++ tailWord_837896).sum := by decide
  have hdescent : baseEnd_837896 < baseStart_837896 := by decide
  rcases family_descends (prefixWord ++ tailWord_837896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837900 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_837900 : Nat := 118140960795 + 837900 * 2 ^ 59
def prefixEnd_837900 : Nat := 4983230072969 + 3 ^ 40 * 837900 * 2
def baseEnd_837900 : Nat := 382440391468779507641399

theorem tailTrace_837900 : CollatzResearch.WordTrace tailWord_837900 prefixEnd_837900 382440391468779507641399 := by
  unfold tailWord_837900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280361832219438386091577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20373815776292584514788769 15280361832219438386091577)
  ·
    refine ⟨11460271374164578789568683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15280361832219438386091577 11460271374164578789568683)
    ·
      refine ⟨17190407061246868184353025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11460271374164578789568683 17190407061246868184353025)
      ·
        refine ⟨12892805295935151138264769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17190407061246868184353025 12892805295935151138264769)
        ·
          refine ⟨9669603971951363353698577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12892805295935151138264769 9669603971951363353698577)
          ·
            refine ⟨7252202978963522515273933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9669603971951363353698577 7252202978963522515273933)
            ·
              refine ⟨2719576117111320943227725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7252202978963522515273933 2719576117111320943227725)
              ·
                refine ⟨1019841043916745353710397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2719576117111320943227725 1019841043916745353710397)
                ·
                  refine ⟨382440391468779507641399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019841043916745353710397 382440391468779507641399)
                  ·
                    rfl

theorem cell20_837900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_837900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837900 prefixEnd_837900 := by exact prefixLift 837900
  have htrace : WordTrace (prefixWord ++ tailWord_837900) baseStart_837900 baseEnd_837900 := by
    simpa [prefixWord, tailWord_837900, baseEnd_837900] using wordTrace_append hprefix tailTrace_837900
  have hstable : (prefixWord ++ tailWord_837900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837900).length < 2 ^ (prefixWord ++ tailWord_837900).sum := by decide
  have hdescent : baseEnd_837900 < baseStart_837900 := by decide
  rcases family_descends (prefixWord ++ tailWord_837900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837921 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_837921 : Nat := 118140960795 + 837921 * 2 ^ 59
def prefixEnd_837921 : Nat := 4983230072969 + 3 ^ 40 * 837921 * 2
def baseEnd_837921 : Nat := 382449976440996767941313

theorem tailTrace_837921 : CollatzResearch.WordTrace tailWord_837921 prefixEnd_837921 382449976440996767941313 := by
  unfold tailWord_837921
  simp only [CollatzResearch.WordTrace]
  refine ⟨30561489597362797358697617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20374326398241864905798411 30561489597362797358697617)
  ·
    refine ⟨22921117198022098019023213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30561489597362797358697617 22921117198022098019023213)
    ·
      refine ⟨8595418949258286757133705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22921117198022098019023213 8595418949258286757133705)
      ·
        refine ⟨6446564211943715067850279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8595418949258286757133705 6446564211943715067850279)
        ·
          refine ⟨9669846317915572601775419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6446564211943715067850279 9669846317915572601775419)
          ·
            refine ⟨14504769476873358902663129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669846317915572601775419 14504769476873358902663129)
            ·
              refine ⟨10878577107655019176997347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14504769476873358902663129 10878577107655019176997347)
              ·
                refine ⟨16317865661482528765496021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10878577107655019176997347 16317865661482528765496021)
                ·
                  refine ⟨382449976440996767941313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16317865661482528765496021 382449976440996767941313)
                  ·
                    rfl

theorem cell20_837921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_837921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837921 prefixEnd_837921 := by exact prefixLift 837921
  have htrace : WordTrace (prefixWord ++ tailWord_837921) baseStart_837921 baseEnd_837921 := by
    simpa [prefixWord, tailWord_837921, baseEnd_837921] using wordTrace_append hprefix tailTrace_837921
  have hstable : (prefixWord ++ tailWord_837921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837921).length < 2 ^ (prefixWord ++ tailWord_837921).sum := by decide
  have hdescent : baseEnd_837921 < baseStart_837921 := by decide
  rcases family_descends (prefixWord ++ tailWord_837921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837927 : List Nat := [1, 1, 8, 1, 2, 7]
def baseStart_837927 : Nat := 118140960795 + 837927 * 2 ^ 59
def prefixEnd_837927 : Nat := 4983230072969 + 3 ^ 40 * 837927 * 2
def baseEnd_837927 : Nat := 14164915370536570879307

theorem tailTrace_837927 : CollatzResearch.WordTrace tailWord_837927 prefixEnd_837927 14164915370536570879307 := by
  unfold tailWord_837927
  simp only [CollatzResearch.WordTrace]
  refine ⟨30561708435341060383416035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20374472290227373588944023 30561708435341060383416035)
  ·
    refine ⟨45842562653011590575124053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30561708435341060383416035 45842562653011590575124053)
    ·
      refine ⟨537217531089979577052235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 45842562653011590575124053 537217531089979577052235)
      ·
        refine ⟨805826296634969365578353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537217531089979577052235 805826296634969365578353)
        ·
          refine ⟨604369722476227024183765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805826296634969365578353 604369722476227024183765)
          ·
            refine ⟨14164915370536570879307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 604369722476227024183765 14164915370536570879307)
            ·
              rfl

theorem cell20_837927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 7].length) (baseStart_837927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837927 prefixEnd_837927 := by exact prefixLift 837927
  have htrace : WordTrace (prefixWord ++ tailWord_837927) baseStart_837927 baseEnd_837927 := by
    simpa [prefixWord, tailWord_837927, baseEnd_837927] using wordTrace_append hprefix tailTrace_837927
  have hstable : (prefixWord ++ tailWord_837927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837927).length < 2 ^ (prefixWord ++ tailWord_837927).sum := by decide
  have hdescent : baseEnd_837927 < baseStart_837927 := by decide
  rcases family_descends (prefixWord ++ tailWord_837927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837937 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 2]
def baseStart_837937 : Nat := 118140960795 + 837937 * 2 ^ 59
def prefixEnd_837937 : Nat := 4983230072969 + 3 ^ 40 * 837937 * 2
def baseEnd_837937 : Nat := 382457279276971823407915

theorem tailTrace_837937 : CollatzResearch.WordTrace tailWord_837937 prefixEnd_837937 382457279276971823407915 := by
  unfold tailWord_837937
  simp only [CollatzResearch.WordTrace]
  refine ⟨30562073165304832091280065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20374715443536554727520043 30562073165304832091280065)
  ·
    refine ⟨22921554873978624068460049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30562073165304832091280065 22921554873978624068460049)
    ·
      refine ⟨17191166155483968051345037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22921554873978624068460049 17191166155483968051345037)
      ·
        refine ⟨6446687308306488019254389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17191166155483968051345037 6446687308306488019254389)
        ·
          refine ⟨604376935153733251805099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6446687308306488019254389 604376935153733251805099)
          ·
            refine ⟨906565402730599877707649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604376935153733251805099 906565402730599877707649)
            ·
              refine ⟨679924052047949908280737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906565402730599877707649 679924052047949908280737)
              ·
                refine ⟨509943039035962431210553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679924052047949908280737 509943039035962431210553)
                ·
                  refine ⟨382457279276971823407915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509943039035962431210553 382457279276971823407915)
                  ·
                    rfl

theorem cell20_837937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_837937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837937 prefixEnd_837937 := by exact prefixLift 837937
  have htrace : WordTrace (prefixWord ++ tailWord_837937) baseStart_837937 baseEnd_837937 := by
    simpa [prefixWord, tailWord_837937, baseEnd_837937] using wordTrace_append hprefix tailTrace_837937
  have hstable : (prefixWord ++ tailWord_837937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837937).length < 2 ^ (prefixWord ++ tailWord_837937).sum := by decide
  have hdescent : baseEnd_837937 < baseStart_837937 := by decide
  rcases family_descends (prefixWord ++ tailWord_837937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837969 : List Nat := [1, 2, 2, 1, 4, 3, 3, 4]
def baseStart_837969 : Nat := 118140960795 + 837969 * 2 ^ 59
def prefixEnd_837969 : Nat := 4983230072969 + 3 ^ 40 * 837969 * 2
def baseEnd_837969 : Nat := 127490628316307311447039

theorem tailTrace_837969 : CollatzResearch.WordTrace tailWord_837969 prefixEnd_837969 127490628316307311447039 := by
  unfold tailWord_837969
  simp only [CollatzResearch.WordTrace]
  refine ⟨30563240301188901556444961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20375493534125934370963307 30563240301188901556444961)
  ·
    refine ⟨22922430225891676167333721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30563240301188901556444961 22922430225891676167333721)
    ·
      refine ⟨17191822669418757125500291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22922430225891676167333721 17191822669418757125500291)
      ·
        refine ⟨25787734004128135688250437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17191822669418757125500291 25787734004128135688250437)
        ·
          refine ⟨4835200125774025441546957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25787734004128135688250437 4835200125774025441546957)
          ·
            refine ⟨1813200047165259540580109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4835200125774025441546957 1813200047165259540580109)
            ·
              refine ⟨679950017686972327717541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1813200047165259540580109 679950017686972327717541)
              ·
                refine ⟨127490628316307311447039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679950017686972327717541 127490628316307311447039)
                ·
                  rfl

theorem cell20_837969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_837969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837969 prefixEnd_837969 := by exact prefixLift 837969
  have htrace : WordTrace (prefixWord ++ tailWord_837969) baseStart_837969 baseEnd_837969 := by
    simpa [prefixWord, tailWord_837969, baseEnd_837969] using wordTrace_append hprefix tailTrace_837969
  have hstable : (prefixWord ++ tailWord_837969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837969).length < 2 ^ (prefixWord ++ tailWord_837969).sum := by decide
  have hdescent : baseEnd_837969 < baseStart_837969 := by decide
  rcases family_descends (prefixWord ++ tailWord_837969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837982 : List Nat := [4, 4, 2, 1, 1, 1, 7]
def baseStart_837982 : Nat := 118140960795 + 837982 * 2 ^ 59
def prefixEnd_837982 : Nat := 4983230072969 + 3 ^ 40 * 837982 * 2
def baseEnd_837982 : Nat := 42497535389239074100859

theorem tailTrace_837982 : CollatzResearch.WordTrace tailWord_837982 prefixEnd_837982 42497535389239074100859 := by
  unfold tailWord_837982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820464306267725597083525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20375809633427869851112133 3820464306267725597083525)
  ·
    refine ⟨716337057425198549453161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3820464306267725597083525 716337057425198549453161)
    ·
      refine ⟨537252793068898912089871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 716337057425198549453161 537252793068898912089871)
      ·
        refine ⟨805879189603348368134807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537252793068898912089871 805879189603348368134807)
        ·
          refine ⟨1208818784405022552202211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805879189603348368134807 1208818784405022552202211)
          ·
            refine ⟨1813228176607533828303317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208818784405022552202211 1813228176607533828303317)
            ·
              refine ⟨42497535389239074100859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1813228176607533828303317 42497535389239074100859)
              ·
                rfl

theorem cell20_837982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 7].length) (baseStart_837982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_837982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_837982 prefixEnd_837982 := by exact prefixLift 837982
  have htrace : WordTrace (prefixWord ++ tailWord_837982) baseStart_837982 baseEnd_837982 := by
    simpa [prefixWord, tailWord_837982, baseEnd_837982] using wordTrace_append hprefix tailTrace_837982
  have hstable : (prefixWord ++ tailWord_837982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837982).length < 2 ^ (prefixWord ++ tailWord_837982).sum := by decide
  have hdescent : baseEnd_837982 < baseStart_837982 := by decide
  rcases family_descends (prefixWord ++ tailWord_837982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838000 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 2]
def baseStart_838000 : Nat := 118140960795 + 838000 * 2 ^ 59
def prefixEnd_838000 : Nat := 4983230072969 + 3 ^ 40 * 838000 * 2
def baseEnd_838000 : Nat := 382486034193623604307657

theorem tailTrace_838000 : CollatzResearch.WordTrace tailWord_838000 prefixEnd_838000 382486034193623604307657 := by
  unfold tailWord_838000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15282185482038296925411727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20376247309384395900548969 15282185482038296925411727)
  ·
    refine ⟨22923278223057445388117591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15282185482038296925411727 22923278223057445388117591)
    ·
      refine ⟨34384917334586168082176387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22923278223057445388117591 34384917334586168082176387)
      ·
        refine ⟨51577376001879252123264581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34384917334586168082176387 51577376001879252123264581)
        ·
          refine ⟨9670758000352359773112109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51577376001879252123264581 9670758000352359773112109)
          ·
            refine ⟨3626534250132134914917041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9670758000352359773112109 3626534250132134914917041)
            ·
              refine ⟨2719900687599101186187781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626534250132134914917041 2719900687599101186187781)
              ·
                refine ⟨509981378924831472410209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2719900687599101186187781 509981378924831472410209)
                ·
                  refine ⟨382486034193623604307657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509981378924831472410209 382486034193623604307657)
                  ·
                    rfl

theorem cell20_838000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_838000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838000 prefixEnd_838000 := by exact prefixLift 838000
  have htrace : WordTrace (prefixWord ++ tailWord_838000) baseStart_838000 baseEnd_838000 := by
    simpa [prefixWord, tailWord_838000, baseEnd_838000] using wordTrace_append hprefix tailTrace_838000
  have hstable : (prefixWord ++ tailWord_838000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838000).length < 2 ^ (prefixWord ++ tailWord_838000).sum := by decide
  have hdescent : baseEnd_838000 < baseStart_838000 := by decide
  rcases family_descends (prefixWord ++ tailWord_838000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838028 : List Nat := [2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_838028 : Nat := 118140960795 + 838028 * 2 ^ 59
def prefixEnd_838028 : Nat := 4983230072969 + 3 ^ 40 * 838028 * 2
def baseEnd_838028 : Nat := 127499604718859983791403

theorem tailTrace_838028 : CollatzResearch.WordTrace tailWord_838028 prefixEnd_838028 127499604718859983791403 := by
  unfold tailWord_838028
  simp only [CollatzResearch.WordTrace]
  refine ⟨15282696103987577316421369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20376928138650103088561825 15282696103987577316421369)
  ·
    refine ⟨11462022077990682987316027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15282696103987577316421369 11462022077990682987316027)
    ·
      refine ⟨17193033116986024480974041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11462022077990682987316027 17193033116986024480974041)
      ·
        refine ⟨12894774837739518360730531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17193033116986024480974041 12894774837739518360730531)
        ·
          refine ⟨19342162256609277541095797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894774837739518360730531 19342162256609277541095797)
          ·
            refine ⟨1813327711557119769477731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19342162256609277541095797 1813327711557119769477731)
            ·
              refine ⟨2719991567335679654216597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813327711557119769477731 2719991567335679654216597)
              ·
                refine ⟨127499604718859983791403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2719991567335679654216597 127499604718859983791403)
                ·
                  rfl

theorem cell20_838028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_838028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838028 prefixEnd_838028 := by exact prefixLift 838028
  have htrace : WordTrace (prefixWord ++ tailWord_838028) baseStart_838028 baseEnd_838028 := by
    simpa [prefixWord, tailWord_838028, baseEnd_838028] using wordTrace_append hprefix tailTrace_838028
  have hstable : (prefixWord ++ tailWord_838028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838028).length < 2 ^ (prefixWord ++ tailWord_838028).sum := by decide
  have hdescent : baseEnd_838028 < baseStart_838028 := by decide
  rcases family_descends (prefixWord ++ tailWord_838028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838045 : List Nat := [1, 4, 2, 1, 4, 2, 6]
def baseStart_838045 : Nat := 118140960795 + 838045 * 2 ^ 59
def prefixEnd_838045 : Nat := 4983230072969 + 3 ^ 40 * 838045 * 2
def baseEnd_838045 : Nat := 42500730379978160867497

theorem tailTrace_838045 : CollatzResearch.WordTrace tailWord_838045 prefixEnd_838045 42500730379978160867497 := by
  unfold tailWord_838045
  simp only [CollatzResearch.WordTrace]
  refine ⟨30566012248913566536211589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20377341499275711024141059 30566012248913566536211589)
  ·
    refine ⟨5731127296671293725539673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30566012248913566536211589 5731127296671293725539673)
    ·
      refine ⟨4298345472503470294154755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5731127296671293725539673 4298345472503470294154755)
      ·
        refine ⟨6447518208755205441232133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298345472503470294154755 6447518208755205441232133)
        ·
          refine ⟨1208909664141601020231025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6447518208755205441232133 1208909664141601020231025)
          ·
            refine ⟨906682248106200765173269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208909664141601020231025 906682248106200765173269)
            ·
              refine ⟨42500730379978160867497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 906682248106200765173269 42500730379978160867497)
              ·
                rfl

theorem cell20_838045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_838045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838045 prefixEnd_838045 := by exact prefixLift 838045
  have htrace : WordTrace (prefixWord ++ tailWord_838045) baseStart_838045 baseEnd_838045 := by
    simpa [prefixWord, tailWord_838045, baseEnd_838045] using wordTrace_append hprefix tailTrace_838045
  have hstable : (prefixWord ++ tailWord_838045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838045).length < 2 ^ (prefixWord ++ tailWord_838045).sum := by decide
  have hdescent : baseEnd_838045 < baseStart_838045 := by decide
  rcases family_descends (prefixWord ++ tailWord_838045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838066 : List Nat := [3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_838066 : Nat := 118140960795 + 838066 * 2 ^ 59
def prefixEnd_838066 : Nat := 4983230072969 + 3 ^ 40 * 838066 * 2
def baseEnd_838066 : Nat := 127505386130673569369129

theorem tailTrace_838066 : CollatzResearch.WordTrace tailWord_838066 prefixEnd_838066 127505386130673569369129 := by
  unfold tailWord_838066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641694545459371780681513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20377852121224991415150701 7641694545459371780681513)
  ·
    refine ⟨5731270909094528835511135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7641694545459371780681513 5731270909094528835511135)
    ·
      refine ⟨8596906363641793253266703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731270909094528835511135 8596906363641793253266703)
      ·
        refine ⟨12895359545462689879900055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8596906363641793253266703 12895359545462689879900055)
        ·
          refine ⟨19343039318194034819850083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12895359545462689879900055 19343039318194034819850083)
          ·
            refine ⟨29014558977291052229775125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19343039318194034819850083 29014558977291052229775125)
            ·
              refine ⟨1360057452060518073270709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29014558977291052229775125 1360057452060518073270709)
              ·
                refine ⟨127505386130673569369129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360057452060518073270709 127505386130673569369129)
                ·
                  rfl

theorem cell20_838066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_838066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838066 prefixEnd_838066 := by exact prefixLift 838066
  have htrace : WordTrace (prefixWord ++ tailWord_838066) baseStart_838066 baseEnd_838066 := by
    simpa [prefixWord, tailWord_838066, baseEnd_838066] using wordTrace_append hprefix tailTrace_838066
  have hstable : (prefixWord ++ tailWord_838066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838066).length < 2 ^ (prefixWord ++ tailWord_838066).sum := by decide
  have hdescent : baseEnd_838066 < baseStart_838066 := by decide
  rcases family_descends (prefixWord ++ tailWord_838066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838069 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_838069 : Nat := 118140960795 + 838069 * 2 ^ 59
def prefixEnd_838069 : Nat := 4983230072969 + 3 ^ 40 * 838069 * 2
def baseEnd_838069 : Nat := 382517527673766031007375

theorem tailTrace_838069 : CollatzResearch.WordTrace tailWord_838069 prefixEnd_838069 382517527673766031007375 := by
  unfold tailWord_838069
  simp only [CollatzResearch.WordTrace]
  refine ⟨30566887600826618635085261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20377925067217745756723507 30566887600826618635085261)
  ·
    refine ⟨11462582850309981988156973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30566887600826618635085261 11462582850309981988156973)
    ·
      refine ⟨4298468568866243245558865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11462582850309981988156973 4298468568866243245558865)
      ·
        refine ⟨3223851426649682434169149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4298468568866243245558865 3223851426649682434169149)
        ·
          refine ⟨1208944284993630912813431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3223851426649682434169149 1208944284993630912813431)
          ·
            refine ⟨1813416427490446369220147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208944284993630912813431 1813416427490446369220147)
            ·
              refine ⟨2720124641235669553830221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813416427490446369220147 2720124641235669553830221)
              ·
                refine ⟨1020046740463376082686333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2720124641235669553830221 1020046740463376082686333)
                ·
                  refine ⟨382517527673766031007375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020046740463376082686333 382517527673766031007375)
                  ·
                    rfl

theorem cell20_838069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_838069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838069 prefixEnd_838069 := by exact prefixLift 838069
  have htrace : WordTrace (prefixWord ++ tailWord_838069) baseStart_838069 baseEnd_838069 := by
    simpa [prefixWord, tailWord_838069, baseEnd_838069] using wordTrace_append hprefix tailTrace_838069
  have hstable : (prefixWord ++ tailWord_838069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838069).length < 2 ^ (prefixWord ++ tailWord_838069).sum := by decide
  have hdescent : baseEnd_838069 < baseStart_838069 := by decide
  rcases family_descends (prefixWord ++ tailWord_838069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838080 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_838080 : Nat := 118140960795 + 838080 * 2 ^ 59
def prefixEnd_838080 : Nat := 4983230072969 + 3 ^ 40 * 838080 * 2
def baseEnd_838080 : Nat := 382522548373498881640663

theorem tailTrace_838080 : CollatzResearch.WordTrace tailWord_838080 prefixEnd_838080 382522548373498881640663 := by
  unfold tailWord_838080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283644401893383756867847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20378192535857845009157129 15283644401893383756867847)
  ·
    refine ⟨22925466602840075635301771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15283644401893383756867847 22925466602840075635301771)
    ·
      refine ⟨34388199904260113452952657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22925466602840075635301771 34388199904260113452952657)
      ·
        refine ⟨25791149928195085089714493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34388199904260113452952657 25791149928195085089714493)
        ·
          refine ⟨9671681223073156908642935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25791149928195085089714493 9671681223073156908642935)
          ·
            refine ⟨14507521834609735362964403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671681223073156908642935 14507521834609735362964403)
            ·
              refine ⟨21761282751914603044446605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14507521834609735362964403 21761282751914603044446605)
              ·
                refine ⟨8160481031967976141667477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21761282751914603044446605 8160481031967976141667477)
                ·
                  refine ⟨382522548373498881640663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8160481031967976141667477 382522548373498881640663)
                  ·
                    rfl

theorem cell20_838080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_838080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838080 prefixEnd_838080 := by exact prefixLift 838080
  have htrace : WordTrace (prefixWord ++ tailWord_838080) baseStart_838080 baseEnd_838080 := by
    simpa [prefixWord, tailWord_838080, baseEnd_838080] using wordTrace_append hprefix tailTrace_838080
  have hstable : (prefixWord ++ tailWord_838080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838080).length < 2 ^ (prefixWord ++ tailWord_838080).sum := by decide
  have hdescent : baseEnd_838080 < baseStart_838080 := by decide
  rcases family_descends (prefixWord ++ tailWord_838080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838163 : List Nat := [1, 1, 1, 2, 1, 5, 9]
def baseStart_838163 : Nat := 118140960795 + 838163 * 2 ^ 59
def prefixEnd_838163 : Nat := 4983230072969 + 3 ^ 40 * 838163 * 2
def baseEnd_838163 : Nat := 42506714648346609097073

theorem tailTrace_838163 : CollatzResearch.WordTrace tailWord_838163 prefixEnd_838163 42506714648346609097073 := by
  unfold tailWord_838163
  simp only [CollatzResearch.WordTrace]
  refine ⟨30570316062486072689007143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20380210708324048459338095 30570316062486072689007143)
  ·
    refine ⟨45855474093729109033510715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30570316062486072689007143 45855474093729109033510715)
    ·
      refine ⟨68783211140593663550266073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45855474093729109033510715 68783211140593663550266073)
      ·
        refine ⟨51587408355445247662699555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68783211140593663550266073 51587408355445247662699555)
        ·
          refine ⟨77381112533167871494049333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51587408355445247662699555 77381112533167871494049333)
          ·
            refine ⟨7254479299984487952567125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77381112533167871494049333 7254479299984487952567125)
            ·
              refine ⟨42506714648346609097073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7254479299984487952567125 42506714648346609097073)
              ·
                rfl

theorem cell20_838163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_838163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838163 prefixEnd_838163 := by exact prefixLift 838163
  have htrace : WordTrace (prefixWord ++ tailWord_838163) baseStart_838163 baseEnd_838163 := by
    simpa [prefixWord, tailWord_838163, baseEnd_838163] using wordTrace_append hprefix tailTrace_838163
  have hstable : (prefixWord ++ tailWord_838163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838163).length < 2 ^ (prefixWord ++ tailWord_838163).sum := by decide
  have hdescent : baseEnd_838163 < baseStart_838163 := by decide
  rcases family_descends (prefixWord ++ tailWord_838163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838173 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_838173 : Nat := 118140960795 + 838173 * 2 ^ 59
def prefixEnd_838173 : Nat := 4983230072969 + 3 ^ 40 * 838173 * 2
def baseEnd_838173 : Nat := 382564996107603891540283

theorem tailTrace_838173 : CollatzResearch.WordTrace tailWord_838173 prefixEnd_838173 382564996107603891540283 := by
  unfold tailWord_838173
  simp only [CollatzResearch.WordTrace]
  refine ⟨30570680792449844396871173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20380453861633229597914115 30570680792449844396871173)
  ·
    refine ⟨5732002648584345824413345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30570680792449844396871173 5732002648584345824413345)
    ·
      refine ⟨4299001986438259368310009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5732002648584345824413345 4299001986438259368310009)
      ·
        refine ⟨3224251489828694526232507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4299001986438259368310009 3224251489828694526232507)
        ·
          refine ⟨4836377234743041789348761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224251489828694526232507 4836377234743041789348761)
          ·
            refine ⟨3627282926057281342011571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4836377234743041789348761 3627282926057281342011571)
            ·
              refine ⟨5440924389085922013017357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627282926057281342011571 5440924389085922013017357)
              ·
                refine ⟨2040346645907220754881509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5440924389085922013017357 2040346645907220754881509)
                ·
                  refine ⟨382564996107603891540283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040346645907220754881509 382564996107603891540283)
                  ·
                    rfl

theorem cell20_838173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_838173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838173 prefixEnd_838173 := by exact prefixLift 838173
  have htrace : WordTrace (prefixWord ++ tailWord_838173) baseStart_838173 baseEnd_838173 := by
    simpa [prefixWord, tailWord_838173, baseEnd_838173] using wordTrace_append hprefix tailTrace_838173
  have hstable : (prefixWord ++ tailWord_838173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838173).length < 2 ^ (prefixWord ++ tailWord_838173).sum := by decide
  have hdescent : baseEnd_838173 < baseStart_838173 := by decide
  rcases family_descends (prefixWord ++ tailWord_838173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838187 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_838187 : Nat := 118140960795 + 838187 * 2 ^ 59
def prefixEnd_838187 : Nat := 4983230072969 + 3 ^ 40 * 838187 * 2
def baseEnd_838187 : Nat := 382571386089082065073559

theorem tailTrace_838187 : CollatzResearch.WordTrace tailWord_838187 prefixEnd_838187 382571386089082065073559 := by
  unfold tailWord_838187
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571191414399124787880815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20380794276266083191920543 30571191414399124787880815)
  ·
    refine ⟨45856787121598687181821223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30571191414399124787880815 45856787121598687181821223)
    ·
      refine ⟨68785180682398030772731835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45856787121598687181821223 68785180682398030772731835)
      ·
        refine ⟨103177771023597046159097753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68785180682398030772731835 103177771023597046159097753)
        ·
          refine ⟨77383328267697784619323315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103177771023597046159097753 77383328267697784619323315)
          ·
            refine ⟨116074992401546676928984973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77383328267697784619323315 116074992401546676928984973)
            ·
              refine ⟨43528122150580003848369365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116074992401546676928984973 43528122150580003848369365)
              ·
                refine ⟨1020190362904218840196157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43528122150580003848369365 1020190362904218840196157)
                ·
                  refine ⟨382571386089082065073559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020190362904218840196157 382571386089082065073559)
                  ·
                    rfl

theorem cell20_838187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_838187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838187 prefixEnd_838187 := by exact prefixLift 838187
  have htrace : WordTrace (prefixWord ++ tailWord_838187) baseStart_838187 baseEnd_838187 := by
    simpa [prefixWord, tailWord_838187, baseEnd_838187] using wordTrace_append hprefix tailTrace_838187
  have hstable : (prefixWord ++ tailWord_838187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838187).length < 2 ^ (prefixWord ++ tailWord_838187).sum := by decide
  have hdescent : baseEnd_838187 < baseStart_838187 := by decide
  rcases family_descends (prefixWord ++ tailWord_838187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838189 : List Nat := [1, 5, 4, 1, 2, 1, 2, 4]
def baseStart_838189 : Nat := 118140960795 + 838189 * 2 ^ 59
def prefixEnd_838189 : Nat := 4983230072969 + 3 ^ 40 * 838189 * 2
def baseEnd_838189 : Nat := 127524099647859649002295

theorem tailTrace_838189 : CollatzResearch.WordTrace tailWord_838189 prefixEnd_838189 127524099647859649002295 := by
  unfold tailWord_838189
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571264360391879129453621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20380842906927919419635747 30571264360391879129453621)
  ·
    refine ⟨2866056033786738668386277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30571264360391879129453621 2866056033786738668386277)
    ·
      refine ⟨537385506335013500322427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2866056033786738668386277 537385506335013500322427)
      ·
        refine ⟨806078259502520250483641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537385506335013500322427 806078259502520250483641)
        ·
          refine ⟨604558694626890187862731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806078259502520250483641 604558694626890187862731)
          ·
            refine ⟨906838041940335281794097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604558694626890187862731 906838041940335281794097)
            ·
              refine ⟨680128531455251461345573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906838041940335281794097 680128531455251461345573)
              ·
                refine ⟨127524099647859649002295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680128531455251461345573 127524099647859649002295)
                ·
                  rfl

theorem cell20_838189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].length) (baseStart_838189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838189 prefixEnd_838189 := by exact prefixLift 838189
  have htrace : WordTrace (prefixWord ++ tailWord_838189) baseStart_838189 baseEnd_838189 := by
    simpa [prefixWord, tailWord_838189, baseEnd_838189] using wordTrace_append hprefix tailTrace_838189
  have hstable : (prefixWord ++ tailWord_838189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838189).length < 2 ^ (prefixWord ++ tailWord_838189).sum := by decide
  have hdescent : baseEnd_838189 < baseStart_838189 := by decide
  rcases family_descends (prefixWord ++ tailWord_838189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838214 : List Nat := [6, 1, 1, 1, 2, 3, 6]
def baseStart_838214 : Nat := 118140960795 + 838214 * 2 ^ 59
def prefixEnd_838214 : Nat := 4983230072969 + 3 ^ 40 * 838214 * 2
def baseEnd_838214 : Nat := 42509301069421107908161

theorem tailTrace_838214 : CollatzResearch.WordTrace tailWord_838214 prefixEnd_838214 42509301069421107908161 := by
  unfold tailWord_838214
  simp only [CollatzResearch.WordTrace]
  refine ⟨955380505790665887472303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20381450790200872266075797 955380505790665887472303)
  ·
    refine ⟨1433070758685998831208455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955380505790665887472303 1433070758685998831208455)
    ·
      refine ⟨2149606138028998246812683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1433070758685998831208455 2149606138028998246812683)
      ·
        refine ⟨3224409207043497370219025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149606138028998246812683 3224409207043497370219025)
        ·
          refine ⟨2418306905282623027664269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3224409207043497370219025 2418306905282623027664269)
          ·
            refine ⟨906865089480983635374101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2418306905282623027664269 906865089480983635374101)
            ·
              refine ⟨42509301069421107908161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 906865089480983635374101 42509301069421107908161)
              ·
                rfl

theorem cell20_838214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 6].length) (baseStart_838214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838214 prefixEnd_838214 := by exact prefixLift 838214
  have htrace : WordTrace (prefixWord ++ tailWord_838214) baseStart_838214 baseEnd_838214 := by
    simpa [prefixWord, tailWord_838214, baseEnd_838214] using wordTrace_append hprefix tailTrace_838214
  have hstable : (prefixWord ++ tailWord_838214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838214).length < 2 ^ (prefixWord ++ tailWord_838214).sum := by decide
  have hdescent : baseEnd_838214 < baseStart_838214 := by decide
  rcases family_descends (prefixWord ++ tailWord_838214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838218 : List Nat := [3, 1, 2, 1, 1, 6, 6]
def baseStart_838218 : Nat := 118140960795 + 838218 * 2 ^ 59
def prefixEnd_838218 : Nat := 4983230072969 + 3 ^ 40 * 838218 * 2
def baseEnd_838218 : Nat := 42509503925975970560011

theorem tailTrace_838218 : CollatzResearch.WordTrace tailWord_838218 prefixEnd_838218 42509503925975970560011 := by
  unfold tailWord_838218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643080519321704270564827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20381548051524544721506205 7643080519321704270564827)
  ·
    refine ⟨11464620778982556405847241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7643080519321704270564827 11464620778982556405847241)
    ·
      refine ⟨8598465584236917304385431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11464620778982556405847241 8598465584236917304385431)
      ·
        refine ⟨12897698376355375956578147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8598465584236917304385431 12897698376355375956578147)
        ·
          refine ⟨19346547564533063934867221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12897698376355375956578147 19346547564533063934867221)
          ·
            refine ⟨906869417087487371946901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19346547564533063934867221 906869417087487371946901)
            ·
              refine ⟨42509503925975970560011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 906869417087487371946901 42509503925975970560011)
              ·
                rfl

theorem cell20_838218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 6].length) (baseStart_838218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838218 prefixEnd_838218 := by exact prefixLift 838218
  have htrace : WordTrace (prefixWord ++ tailWord_838218) baseStart_838218 baseEnd_838218 := by
    simpa [prefixWord, tailWord_838218, baseEnd_838218] using wordTrace_append hprefix tailTrace_838218
  have hstable : (prefixWord ++ tailWord_838218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838218).length < 2 ^ (prefixWord ++ tailWord_838218).sum := by decide
  have hdescent : baseEnd_838218 < baseStart_838218 := by decide
  rcases family_descends (prefixWord ++ tailWord_838218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838225 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_838225 : Nat := 118140960795 + 838225 * 2 ^ 59
def prefixEnd_838225 : Nat := 4983230072969 + 3 ^ 40 * 838225 * 2
def baseEnd_838225 : Nat := 382588730324522821806737

theorem tailTrace_838225 : CollatzResearch.WordTrace tailWord_838225 prefixEnd_838225 382588730324522821806737 := by
  unfold tailWord_838225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30572577388261457277764129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20381718258840971518509419 30572577388261457277764129)
  ·
    refine ⟨22929433041196092958323097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30572577388261457277764129 22929433041196092958323097)
    ·
      refine ⟨17197074780897069718742323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22929433041196092958323097 17197074780897069718742323)
      ·
        refine ⟨25795612171345604578113485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17197074780897069718742323 25795612171345604578113485)
        ·
          refine ⟨9673354564254601716792557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25795612171345604578113485 9673354564254601716792557)
          ·
            refine ⟨3627507961595475643797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9673354564254601716792557 3627507961595475643797209)
            ·
              refine ⟨2720630971196606732847907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3627507961595475643797209 2720630971196606732847907)
              ·
                refine ⟨4080946456794910099271861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720630971196606732847907 4080946456794910099271861)
                ·
                  refine ⟨382588730324522821806737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080946456794910099271861 382588730324522821806737)
                  ·
                    rfl

theorem cell20_838225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_838225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838225 prefixEnd_838225 := by exact prefixLift 838225
  have htrace : WordTrace (prefixWord ++ tailWord_838225) baseStart_838225 baseEnd_838225 := by
    simpa [prefixWord, tailWord_838225, baseEnd_838225] using wordTrace_append hprefix tailTrace_838225
  have hstable : (prefixWord ++ tailWord_838225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838225).length < 2 ^ (prefixWord ++ tailWord_838225).sum := by decide
  have hdescent : baseEnd_838225 < baseStart_838225 := by decide
  rcases family_descends (prefixWord ++ tailWord_838225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838228 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_838228 : Nat := 118140960795 + 838228 * 2 ^ 59
def prefixEnd_838228 : Nat := 4983230072969 + 3 ^ 40 * 838228 * 2
def baseEnd_838228 : Nat := 382590099606268144706725

theorem tailTrace_838228 : CollatzResearch.WordTrace tailWord_838228 prefixEnd_838228 382590099606268144706725 := by
  unfold tailWord_838228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286343403625294395061669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20381791204833725860082225 15286343403625294395061669)
  ·
    refine ⟨2866189388179742699074063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15286343403625294395061669 2866189388179742699074063)
    ·
      refine ⟨4299284082269614048611095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2866189388179742699074063 4299284082269614048611095)
      ·
        refine ⟨6448926123404421072916643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299284082269614048611095 6448926123404421072916643)
        ·
          refine ⟨9673389185106631609374965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448926123404421072916643 9673389185106631609374965)
          ·
            refine ⟨906880236103746713378903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9673389185106631609374965 906880236103746713378903)
            ·
              refine ⟨1360320354155620070068355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906880236103746713378903 1360320354155620070068355)
              ·
                refine ⟨2040480531233430105102533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360320354155620070068355 2040480531233430105102533)
                ·
                  refine ⟨382590099606268144706725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040480531233430105102533 382590099606268144706725)
                  ·
                    rfl

theorem cell20_838228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_838228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838228 prefixEnd_838228 := by exact prefixLift 838228
  have htrace : WordTrace (prefixWord ++ tailWord_838228) baseStart_838228 baseEnd_838228 := by
    simpa [prefixWord, tailWord_838228, baseEnd_838228] using wordTrace_append hprefix tailTrace_838228
  have hstable : (prefixWord ++ tailWord_838228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838228).length < 2 ^ (prefixWord ++ tailWord_838228).sum := by decide
  have hdescent : baseEnd_838228 < baseStart_838228 := by decide
  rcases family_descends (prefixWord ++ tailWord_838228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838277 : List Nat := [1, 3, 1, 1, 4, 10]
def baseStart_838277 : Nat := 118140960795 + 838277 * 2 ^ 59
def prefixEnd_838277 : Nat := 4983230072969 + 3 ^ 40 * 838277 * 2
def baseEnd_838277 : Nat := 14170832020053398224933

theorem tailTrace_838277 : CollatzResearch.WordTrace tailWord_838277 prefixEnd_838277 14170832020053398224933 := by
  unfold tailWord_838277
  simp only [CollatzResearch.WordTrace]
  refine ⟨30574473984073070158657085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20382982656048713439104723 30574473984073070158657085)
  ·
    refine ⟨11465427744027401309496407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30574473984073070158657085 11465427744027401309496407)
    ·
      refine ⟨17198141616041101964244611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11465427744027401309496407 17198141616041101964244611)
      ·
        refine ⟨25797212424061652946366917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17198141616041101964244611 25797212424061652946366917)
        ·
          refine ⟨4836977329511559927443797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25797212424061652946366917 4836977329511559927443797)
          ·
            refine ⟨14170832020053398224933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4836977329511559927443797 14170832020053398224933)
            ·
              rfl

theorem cell20_838277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 10].length) (baseStart_838277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838277 prefixEnd_838277 := by exact prefixLift 838277
  have htrace : WordTrace (prefixWord ++ tailWord_838277) baseStart_838277 baseEnd_838277 := by
    simpa [prefixWord, tailWord_838277, baseEnd_838277] using wordTrace_append hprefix tailTrace_838277
  have hstable : (prefixWord ++ tailWord_838277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838277).length < 2 ^ (prefixWord ++ tailWord_838277).sum := by decide
  have hdescent : baseEnd_838277 < baseStart_838277 := by decide
  rcases family_descends (prefixWord ++ tailWord_838277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838287 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 2]
def baseStart_838287 : Nat := 118140960795 + 838287 * 2 ^ 59
def prefixEnd_838287 : Nat := 4983230072969 + 3 ^ 40 * 838287 * 2
def baseEnd_838287 : Nat := 382617028813926161739817

theorem tailTrace_838287 : CollatzResearch.WordTrace tailWord_838287 prefixEnd_838287 382617028813926161739817 := by
  unfold tailWord_838287
  simp only [CollatzResearch.WordTrace]
  refine ⟨30574838714036841866521115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20383225809357894577680743 30574838714036841866521115)
  ·
    refine ⟨45862258071055262799781673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30574838714036841866521115 45862258071055262799781673)
    ·
      refine ⟨34396693553291447099836255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45862258071055262799781673 34396693553291447099836255)
      ·
        refine ⟨51595040329937170649754383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34396693553291447099836255 51595040329937170649754383)
        ·
          refine ⟨77392560494905755974631575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51595040329937170649754383 77392560494905755974631575)
          ·
            refine ⟨116088840742358633961947363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77392560494905755974631575 116088840742358633961947363)
            ·
              refine ⟨174133261113537950942921045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116088840742358633961947363 174133261113537950942921045)
              ·
                refine ⟨510156038418568215653089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 174133261113537950942921045 510156038418568215653089)
                ·
                  refine ⟨382617028813926161739817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510156038418568215653089 382617028813926161739817)
                  ·
                    rfl

theorem cell20_838287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 2].length) (baseStart_838287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838287 prefixEnd_838287 := by exact prefixLift 838287
  have htrace : WordTrace (prefixWord ++ tailWord_838287) baseStart_838287 baseEnd_838287 := by
    simpa [prefixWord, tailWord_838287, baseEnd_838287] using wordTrace_append hprefix tailTrace_838287
  have hstable : (prefixWord ++ tailWord_838287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838287).length < 2 ^ (prefixWord ++ tailWord_838287).sum := by decide
  have hdescent : baseEnd_838287 < baseStart_838287 := by decide
  rcases family_descends (prefixWord ++ tailWord_838287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838353 : List Nat := [1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_838353 : Nat := 118140960795 + 838353 * 2 ^ 59
def prefixEnd_838353 : Nat := 4983230072969 + 3 ^ 40 * 838353 * 2
def baseEnd_838353 : Nat := 127549051004107755179849

theorem tailTrace_838353 : CollatzResearch.WordTrace tailWord_838353 prefixEnd_838353 127549051004107755179849 := by
  unfold tailWord_838353
  simp only [CollatzResearch.WordTrace]
  refine ⟨30577245931797735138423713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20384830621198490092282475 30577245931797735138423713)
  ·
    refine ⟨22932934448848301353817785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30577245931797735138423713 22932934448848301353817785)
    ·
      refine ⟨17199700836636226015363339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22932934448848301353817785 17199700836636226015363339)
      ·
        refine ⟨25799551254954339023045009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17199700836636226015363339 25799551254954339023045009)
        ·
          refine ⟨19349663441215754267283757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25799551254954339023045009 19349663441215754267283757)
          ·
            refine ⟨7256123790455907850231409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19349663441215754267283757 7256123790455907850231409)
            ·
              refine ⟨5442092842841930887673557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7256123790455907850231409 5442092842841930887673557)
              ·
                refine ⟨127549051004107755179849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5442092842841930887673557 127549051004107755179849)
                ·
                  rfl

theorem cell20_838353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_838353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838353 prefixEnd_838353 := by exact prefixLift 838353
  have htrace : WordTrace (prefixWord ++ tailWord_838353) baseStart_838353 baseEnd_838353 := by
    simpa [prefixWord, tailWord_838353, baseEnd_838353] using wordTrace_append hprefix tailTrace_838353
  have hstable : (prefixWord ++ tailWord_838353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838353).length < 2 ^ (prefixWord ++ tailWord_838353).sum := by decide
  have hdescent : baseEnd_838353 < baseStart_838353 := by decide
  rcases family_descends (prefixWord ++ tailWord_838353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838376 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 2]
def baseStart_838376 : Nat := 118140960795 + 838376 * 2 ^ 59
def prefixEnd_838376 : Nat := 4983230072969 + 3 ^ 40 * 838376 * 2
def baseEnd_838376 : Nat := 382657650839037407772787

theorem tailTrace_838376 : CollatzResearch.WordTrace tailWord_838376 prefixEnd_838376 382657650839037407772787 := by
  unfold tailWord_838376
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289042405357205033255491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20385389873809606711007321 15289042405357205033255491)
  ·
    refine ⟨22933563608035807549883237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15289042405357205033255491 22933563608035807549883237)
    ·
      refine ⟨4300043176506713915603107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22933563608035807549883237 4300043176506713915603107)
      ·
        refine ⟨6450064764760070873404661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4300043176506713915603107 6450064764760070873404661)
        ·
          refine ⟨604693571696256644381687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6450064764760070873404661 604693571696256644381687)
          ·
            refine ⟨907040357544384966572531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604693571696256644381687 907040357544384966572531)
            ·
              refine ⟨1360560536316577449858797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907040357544384966572531 1360560536316577449858797)
              ·
                refine ⟨510210201118716543697049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1360560536316577449858797 510210201118716543697049)
                ·
                  refine ⟨382657650839037407772787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510210201118716543697049 382657650839037407772787)
                  ·
                    rfl

theorem cell20_838376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_838376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838376 prefixEnd_838376 := by exact prefixLift 838376
  have htrace : WordTrace (prefixWord ++ tailWord_838376) baseStart_838376 baseEnd_838376 := by
    simpa [prefixWord, tailWord_838376, baseEnd_838376] using wordTrace_append hprefix tailTrace_838376
  have hstable : (prefixWord ++ tailWord_838376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838376).length < 2 ^ (prefixWord ++ tailWord_838376).sum := by decide
  have hdescent : baseEnd_838376 < baseStart_838376 := by decide
  rcases family_descends (prefixWord ++ tailWord_838376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838408 : List Nat := [2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_838408 : Nat := 118140960795 + 838408 * 2 ^ 59
def prefixEnd_838408 : Nat := 4983230072969 + 3 ^ 40 * 838408 * 2
def baseEnd_838408 : Nat := 127557418836995839568663

theorem tailTrace_838408 : CollatzResearch.WordTrace tailWord_838408 prefixEnd_838408 127557418836995839568663 := by
  unfold tailWord_838408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289625973299239765837939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20386167964398986354450585 15289625973299239765837939)
  ·
    refine ⟨22934438959948859648756909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15289625973299239765837939 22934438959948859648756909)
    ·
      refine ⟨8600414609980822368283841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22934438959948859648756909 8600414609980822368283841)
      ·
        refine ⟨6450310957485616776212881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8600414609980822368283841 6450310957485616776212881)
        ·
          refine ⟨4837733218114212582159661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450310957485616776212881 4837733218114212582159661)
          ·
            refine ⟨1814149956792829718309873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4837733218114212582159661 1814149956792829718309873)
            ·
              refine ⟨1360612467594622288732405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814149956792829718309873 1360612467594622288732405)
              ·
                refine ⟨127557418836995839568663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360612467594622288732405 127557418836995839568663)
                ·
                  rfl

theorem cell20_838408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_838408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838408 prefixEnd_838408 := by exact prefixLift 838408
  have htrace : WordTrace (prefixWord ++ tailWord_838408) baseStart_838408 baseEnd_838408 := by
    simpa [prefixWord, tailWord_838408, baseEnd_838408] using wordTrace_append hprefix tailTrace_838408
  have hstable : (prefixWord ++ tailWord_838408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838408).length < 2 ^ (prefixWord ++ tailWord_838408).sum := by decide
  have hdescent : baseEnd_838408 < baseStart_838408 := by decide
  rcases family_descends (prefixWord ++ tailWord_838408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838415 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_838415 : Nat := 118140960795 + 838415 * 2 ^ 59
def prefixEnd_838415 : Nat := 4983230072969 + 3 ^ 40 * 838415 * 2
def baseEnd_838415 : Nat := 382675451501726605472627

theorem tailTrace_838415 : CollatzResearch.WordTrace tailWord_838415 prefixEnd_838415 382675451501726605472627 := by
  unfold tailWord_838415
  simp only [CollatzResearch.WordTrace]
  refine ⟨30579507257573119727180699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20386338171715413151453799 30579507257573119727180699)
  ·
    refine ⟨45869260886359679590771049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30579507257573119727180699 45869260886359679590771049)
    ·
      refine ⟨34401945664769759693078287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45869260886359679590771049 34401945664769759693078287)
      ·
        refine ⟨51602918497154639539617431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34401945664769759693078287 51602918497154639539617431)
        ·
          refine ⟨77404377745731959309426147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51602918497154639539617431 77404377745731959309426147)
          ·
            refine ⟨116106566618597938964139221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77404377745731959309426147 116106566618597938964139221)
            ·
              refine ⟨2721247655123389194472013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 116106566618597938964139221 2721247655123389194472013)
              ·
                refine ⟨1020467870671270947927005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2721247655123389194472013 1020467870671270947927005)
                ·
                  refine ⟨382675451501726605472627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020467870671270947927005 382675451501726605472627)
                  ·
                    rfl

theorem cell20_838415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_838415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838415 prefixEnd_838415 := by exact prefixLift 838415
  have htrace : WordTrace (prefixWord ++ tailWord_838415) baseStart_838415 baseEnd_838415 := by
    simpa [prefixWord, tailWord_838415, baseEnd_838415] using wordTrace_append hprefix tailTrace_838415
  have hstable : (prefixWord ++ tailWord_838415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838415).length < 2 ^ (prefixWord ++ tailWord_838415).sum := by decide
  have hdescent : baseEnd_838415 < baseStart_838415 := by decide
  rcases family_descends (prefixWord ++ tailWord_838415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838446 : List Nat := [4, 1, 3, 2, 1, 9]
def baseStart_838446 : Nat := 118140960795 + 838446 * 2 ^ 59
def prefixEnd_838446 : Nat := 4983230072969 + 3 ^ 40 * 838446 * 2
def baseEnd_838446 : Nat := 14173688916534380571821

theorem tailTrace_838446 : CollatzResearch.WordTrace tailWord_838446 prefixEnd_838446 14173688916534380571821 := by
  unfold tailWord_838446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822579740057601502694899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20387091946973874681039461 3822579740057601502694899)
  ·
    refine ⟨5733869610086402254042349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3822579740057601502694899 5733869610086402254042349)
    ·
      refine ⟨2150201103782400845265881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5733869610086402254042349 2150201103782400845265881)
      ·
        refine ⟨1612650827836800633949411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2150201103782400845265881 1612650827836800633949411)
        ·
          refine ⟨2418976241755200950924117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612650827836800633949411 2418976241755200950924117)
          ·
            refine ⟨14173688916534380571821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2418976241755200950924117 14173688916534380571821)
            ·
              rfl

theorem cell20_838446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 9].length) (baseStart_838446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838446 prefixEnd_838446 := by exact prefixLift 838446
  have htrace : WordTrace (prefixWord ++ tailWord_838446) baseStart_838446 baseEnd_838446 := by
    simpa [prefixWord, tailWord_838446, baseEnd_838446] using wordTrace_append hprefix tailTrace_838446
  have hstable : (prefixWord ++ tailWord_838446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838446).length < 2 ^ (prefixWord ++ tailWord_838446).sum := by decide
  have hdescent : baseEnd_838446 < baseStart_838446 := by decide
  rcases family_descends (prefixWord ++ tailWord_838446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838460 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_838460 : Nat := 118140960795 + 838460 * 2 ^ 59
def prefixEnd_838460 : Nat := 4983230072969 + 3 ^ 40 * 838460 * 2
def baseEnd_838460 : Nat := 382695990727906448972443

theorem tailTrace_838460 : CollatzResearch.WordTrace tailWord_838460 prefixEnd_838460 382695990727906448972443 := by
  unfold tailWord_838460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15290574271205046206284417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20387432361606728275045889 15290574271205046206284417)
  ·
    refine ⟨11467930703403784654713313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15290574271205046206284417 11467930703403784654713313)
    ·
      refine ⟨8600948027552838491034985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11467930703403784654713313 8600948027552838491034985)
      ·
        refine ⟨6450711020664628868276239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8600948027552838491034985 6450711020664628868276239)
        ·
          refine ⟨9676066530996943302414359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6450711020664628868276239 9676066530996943302414359)
          ·
            refine ⟨14514099796495414953621539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9676066530996943302414359 14514099796495414953621539)
            ·
              refine ⟨21771149694743122430432309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14514099796495414953621539 21771149694743122430432309)
              ·
                refine ⟨2041045283882167727853029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21771149694743122430432309 2041045283882167727853029)
                ·
                  refine ⟨382695990727906448972443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041045283882167727853029 382695990727906448972443)
                  ·
                    rfl

theorem cell20_838460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_838460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838460 prefixEnd_838460 := by exact prefixLift 838460
  have htrace : WordTrace (prefixWord ++ tailWord_838460) baseStart_838460 baseEnd_838460 := by
    simpa [prefixWord, tailWord_838460, baseEnd_838460] using wordTrace_append hprefix tailTrace_838460
  have hstable : (prefixWord ++ tailWord_838460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838460).length < 2 ^ (prefixWord ++ tailWord_838460).sum := by decide
  have hdescent : baseEnd_838460 < baseStart_838460 := by decide
  rcases family_descends (prefixWord ++ tailWord_838460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838515 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 2]
def baseStart_838515 : Nat := 118140960795 + 838515 * 2 ^ 59
def prefixEnd_838515 : Nat := 4983230072969 + 3 ^ 40 * 838515 * 2
def baseEnd_838515 : Nat := 382721094226570702138885

theorem tailTrace_838515 : CollatzResearch.WordTrace tailWord_838515 prefixEnd_838515 382721094226570702138885 := by
  unfold tailWord_838515
  simp only [CollatzResearch.WordTrace]
  refine ⟨30583154557210836805820999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20388769704807224537213999 30583154557210836805820999)
  ·
    refine ⟨45874731835816255208731499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30583154557210836805820999 45874731835816255208731499)
    ·
      refine ⟨68812097753724382813097249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45874731835816255208731499 68812097753724382813097249)
      ·
        refine ⟨51609073315293287109822937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68812097753724382813097249 51609073315293287109822937)
        ·
          refine ⟨38706804986469965332367203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51609073315293287109822937 38706804986469965332367203)
          ·
            refine ⟨58060207479704947998550805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38706804986469965332367203 58060207479704947998550805)
            ·
              refine ⟨2721572225611169437432069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58060207479704947998550805 2721572225611169437432069)
              ·
                refine ⟨510294792302094269518513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2721572225611169437432069 510294792302094269518513)
                ·
                  refine ⟨382721094226570702138885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510294792302094269518513 382721094226570702138885)
                  ·
                    rfl

theorem cell20_838515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 2].length) (baseStart_838515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838515 prefixEnd_838515 := by exact prefixLift 838515
  have htrace : WordTrace (prefixWord ++ tailWord_838515) baseStart_838515 baseEnd_838515 := by
    simpa [prefixWord, tailWord_838515, baseEnd_838515] using wordTrace_append hprefix tailTrace_838515
  have hstable : (prefixWord ++ tailWord_838515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838515).length < 2 ^ (prefixWord ++ tailWord_838515).sum := by decide
  have hdescent : baseEnd_838515 < baseStart_838515 := by decide
  rcases family_descends (prefixWord ++ tailWord_838515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838580 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_838580 : Nat := 118140960795 + 838580 * 2 ^ 59
def prefixEnd_838580 : Nat := 4983230072969 + 3 ^ 40 * 838580 * 2
def baseEnd_838580 : Nat := 382750761997719364971953

theorem tailTrace_838580 : CollatzResearch.WordTrace tailWord_838580 prefixEnd_838580 382750761997719364971953 := by
  unfold tailWord_838580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15292762650987676453468597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20390350201316901937958129 15292762650987676453468597)
  ·
    refine ⟨1433696498530094667512681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15292762650987676453468597 1433696498530094667512681)
    ·
      refine ⟨1075272373897571000634511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1433696498530094667512681 1075272373897571000634511)
      ·
        refine ⟨1612908560846356500951767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075272373897571000634511 1612908560846356500951767)
        ·
          refine ⟨2419362841269534751427651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612908560846356500951767 2419362841269534751427651)
          ·
            refine ⟨3629044261904302127141477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419362841269534751427651 3629044261904302127141477)
            ·
              refine ⟨680445799107056648839027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3629044261904302127141477 680445799107056648839027)
              ·
                refine ⟨1020668698660584973258541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680445799107056648839027 1020668698660584973258541)
                ·
                  refine ⟨382750761997719364971953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020668698660584973258541 382750761997719364971953)
                  ·
                    rfl

theorem cell20_838580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_838580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838580 prefixEnd_838580 := by exact prefixLift 838580
  have htrace : WordTrace (prefixWord ++ tailWord_838580) baseStart_838580 baseEnd_838580 := by
    simpa [prefixWord, tailWord_838580, baseEnd_838580] using wordTrace_append hprefix tailTrace_838580
  have hstable : (prefixWord ++ tailWord_838580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838580).length < 2 ^ (prefixWord ++ tailWord_838580).sum := by decide
  have hdescent : baseEnd_838580 < baseStart_838580 := by decide
  rcases family_descends (prefixWord ++ tailWord_838580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838584 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_838584 : Nat := 118140960795 + 838584 * 2 ^ 59
def prefixEnd_838584 : Nat := 4983230072969 + 3 ^ 40 * 838584 * 2
def baseEnd_838584 : Nat := 382752587706713128838603

theorem tailTrace_838584 : CollatzResearch.WordTrace tailWord_838584 prefixEnd_838584 382752587706713128838603 := by
  unfold tailWord_838584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15292835596980430795041403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20390447462640574393388537 15292835596980430795041403)
  ·
    refine ⟨22939253395470646192562105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15292835596980430795041403 22939253395470646192562105)
    ·
      refine ⟨17204440046602984644421579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22939253395470646192562105 17204440046602984644421579)
      ·
        refine ⟨25806660069904476966632369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17204440046602984644421579 25806660069904476966632369)
        ·
          refine ⟨19354995052428357724974277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25806660069904476966632369 19354995052428357724974277)
          ·
            refine ⟨3629061572330317073432677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19354995052428357724974277 3629061572330317073432677)
            ·
              refine ⟨680449044811934451268627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3629061572330317073432677 680449044811934451268627)
              ·
                refine ⟨1020673567217901676902941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680449044811934451268627 1020673567217901676902941)
                ·
                  refine ⟨382752587706713128838603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020673567217901676902941 382752587706713128838603)
                  ·
                    rfl

theorem cell20_838584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_838584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838584 prefixEnd_838584 := by exact prefixLift 838584
  have htrace : WordTrace (prefixWord ++ tailWord_838584) baseStart_838584 baseEnd_838584 := by
    simpa [prefixWord, tailWord_838584, baseEnd_838584] using wordTrace_append hprefix tailTrace_838584
  have hstable : (prefixWord ++ tailWord_838584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838584).length < 2 ^ (prefixWord ++ tailWord_838584).sum := by decide
  have hdescent : baseEnd_838584 < baseStart_838584 := by decide
  rcases family_descends (prefixWord ++ tailWord_838584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838633 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_838633 : Nat := 118140960795 + 838633 * 2 ^ 59
def prefixEnd_838633 : Nat := 4983230072969 + 3 ^ 40 * 838633 * 2
def baseEnd_838633 : Nat := 382774952641886736205069

theorem tailTrace_838633 : CollatzResearch.WordTrace tailWord_838633 prefixEnd_838633 382774952641886736205069 := by
  unfold tailWord_838633
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587458370783342958616553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20391638913855561972411035 30587458370783342958616553)
  ·
    refine ⟨22940593778087507218962415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30587458370783342958616553 22940593778087507218962415)
    ·
      refine ⟨34410890667131260828443623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22940593778087507218962415 34410890667131260828443623)
      ·
        refine ⟨51616336000696891242665435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34410890667131260828443623 51616336000696891242665435)
        ·
          refine ⟨77424504001045336863998153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51616336000696891242665435 77424504001045336863998153)
          ·
            refine ⟨58068378000784002647998615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77424504001045336863998153 58068378000784002647998615)
            ·
              refine ⟨87102567001176003971997923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58068378000784002647998615 87102567001176003971997923)
              ·
                refine ⟨130653850501764005957996885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87102567001176003971997923 130653850501764005957996885)
                ·
                  refine ⟨382774952641886736205069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130653850501764005957996885 382774952641886736205069)
                  ·
                    rfl

theorem cell20_838633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_838633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838633 prefixEnd_838633 := by exact prefixLift 838633
  have htrace : WordTrace (prefixWord ++ tailWord_838633) baseStart_838633 baseEnd_838633 := by
    simpa [prefixWord, tailWord_838633, baseEnd_838633] using wordTrace_append hprefix tailTrace_838633
  have hstable : (prefixWord ++ tailWord_838633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838633).length < 2 ^ (prefixWord ++ tailWord_838633).sum := by decide
  have hdescent : baseEnd_838633 < baseStart_838633 := by decide
  rcases family_descends (prefixWord ++ tailWord_838633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838667 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 2]
def baseStart_838667 : Nat := 118140960795 + 838667 * 2 ^ 59
def prefixEnd_838667 : Nat := 4983230072969 + 3 ^ 40 * 838667 * 2
def baseEnd_838667 : Nat := 382790471168333729071597

theorem tailTrace_838667 : CollatzResearch.WordTrace tailWord_838667 prefixEnd_838667 382790471168333729071597 := by
  unfold tailWord_838667
  simp only [CollatzResearch.WordTrace]
  refine ⟨30588698452660166765354255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392465635106777843569503 30588698452660166765354255)
  ·
    refine ⟨45883047678990250148031383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30588698452660166765354255 45883047678990250148031383)
    ·
      refine ⟨68824571518485375222047075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45883047678990250148031383 68824571518485375222047075)
      ·
        refine ⟨103236857277728062833070613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68824571518485375222047075 103236857277728062833070613)
        ·
          refine ⟨4839227684893502945300185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103236857277728062833070613 4839227684893502945300185)
          ·
            refine ⟨3629420763670127208975139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4839227684893502945300185 3629420763670127208975139)
            ·
              refine ⟨5444131145505190813462709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629420763670127208975139 5444131145505190813462709)
              ·
                refine ⟨510387294891111638762129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5444131145505190813462709 510387294891111638762129)
                ·
                  refine ⟨382790471168333729071597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510387294891111638762129 382790471168333729071597)
                  ·
                    rfl

theorem cell20_838667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 2].length) (baseStart_838667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838667 prefixEnd_838667 := by exact prefixLift 838667
  have htrace : WordTrace (prefixWord ++ tailWord_838667) baseStart_838667 baseEnd_838667 := by
    simpa [prefixWord, tailWord_838667, baseEnd_838667] using wordTrace_append hprefix tailTrace_838667
  have hstable : (prefixWord ++ tailWord_838667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838667).length < 2 ^ (prefixWord ++ tailWord_838667).sum := by decide
  have hdescent : baseEnd_838667 < baseStart_838667 := by decide
  rcases family_descends (prefixWord ++ tailWord_838667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838681 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_838681 : Nat := 118140960795 + 838681 * 2 ^ 59
def prefixEnd_838681 : Nat := 4983230072969 + 3 ^ 40 * 838681 * 2
def baseEnd_838681 : Nat := 382796861149811902604873

theorem tailTrace_838681 : CollatzResearch.WordTrace tailWord_838681 prefixEnd_838681 382796861149811902604873 := by
  unfold tailWord_838681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589209074609447156363897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392806049739631437575931 30589209074609447156363897)
  ·
    refine ⟨22941906805957085367272923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30589209074609447156363897 22941906805957085367272923)
    ·
      refine ⟨34412860208935628050909385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22941906805957085367272923 34412860208935628050909385)
      ·
        refine ⟨25809645156701721038182039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34412860208935628050909385 25809645156701721038182039)
        ·
          refine ⟨38714467735052581557273059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25809645156701721038182039 38714467735052581557273059)
          ·
            refine ⟨58071701602578872335909589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38714467735052581557273059 58071701602578872335909589)
            ·
              refine ⟨1361055506310442320372881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58071701602578872335909589 1361055506310442320372881)
              ·
                refine ⟨1020791629732831740279661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361055506310442320372881 1020791629732831740279661)
                ·
                  refine ⟨382796861149811902604873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020791629732831740279661 382796861149811902604873)
                  ·
                    rfl

theorem cell20_838681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_838681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838681 prefixEnd_838681 := by exact prefixLift 838681
  have htrace : WordTrace (prefixWord ++ tailWord_838681) baseStart_838681 baseEnd_838681 := by
    simpa [prefixWord, tailWord_838681, baseEnd_838681] using wordTrace_append hprefix tailTrace_838681
  have hstable : (prefixWord ++ tailWord_838681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838681).length < 2 ^ (prefixWord ++ tailWord_838681).sum := by decide
  have hdescent : baseEnd_838681 < baseStart_838681 := by decide
  rcases family_descends (prefixWord ++ tailWord_838681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838708 : List Nat := [2, 5, 1, 2, 1, 3, 2, 4]
def baseStart_838708 : Nat := 118140960795 + 838708 * 2 ^ 59
def prefixEnd_838708 : Nat := 4983230072969 + 3 ^ 40 * 838708 * 2
def baseEnd_838708 : Nat := 127603061561839936234921

theorem tailTrace_838708 : CollatzResearch.WordTrace tailWord_838708 prefixEnd_838708 127603061561839936234921 := by
  unfold tailWord_838708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15295096922755815383798389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20393462563674420511731185 15295096922755815383798389)
  ·
    refine ⟨1433915336508357692231099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15295096922755815383798389 1433915336508357692231099)
    ·
      refine ⟨2150873004762536538346649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1433915336508357692231099 2150873004762536538346649)
      ·
        refine ⟨1613154753571902403759987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2150873004762536538346649 1613154753571902403759987)
        ·
          refine ⟨2419732130357853605639981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613154753571902403759987 2419732130357853605639981)
          ·
            refine ⟨907399548884195102114993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2419732130357853605639981 907399548884195102114993)
            ·
              refine ⟨680549661663146326586245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907399548884195102114993 680549661663146326586245)
              ·
                refine ⟨127603061561839936234921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680549661663146326586245 127603061561839936234921)
                ·
                  rfl

theorem cell20_838708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_838708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838708 prefixEnd_838708 := by exact prefixLift 838708
  have htrace : WordTrace (prefixWord ++ tailWord_838708) baseStart_838708 baseEnd_838708 := by
    simpa [prefixWord, tailWord_838708, baseEnd_838708] using wordTrace_append hprefix tailTrace_838708
  have hstable : (prefixWord ++ tailWord_838708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838708).length < 2 ^ (prefixWord ++ tailWord_838708).sum := by decide
  have hdescent : baseEnd_838708 < baseStart_838708 := by decide
  rcases family_descends (prefixWord ++ tailWord_838708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838712 : List Nat := [2, 1, 2, 1, 5, 1, 4, 4]
def baseStart_838712 : Nat := 118140960795 + 838712 * 2 ^ 59
def prefixEnd_838712 : Nat := 4983230072969 + 3 ^ 40 * 838712 * 2
def baseEnd_838712 : Nat := 127603670131504524190471

theorem tailTrace_838712 : CollatzResearch.WordTrace tailWord_838712 prefixEnd_838712 127603670131504524190471 := by
  unfold tailWord_838712
  simp only [CollatzResearch.WordTrace]
  refine ⟨15295169868748569725371195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20393559824998092967161593 15295169868748569725371195)
  ·
    refine ⟨22942754803122854588056793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15295169868748569725371195 22942754803122854588056793)
    ·
      refine ⟨17207066102342140941042595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22942754803122854588056793 17207066102342140941042595)
      ·
        refine ⟨25810599153513211411563893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17207066102342140941042595 25810599153513211411563893)
        ·
          refine ⟨2419743670641863569834115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25810599153513211411563893 2419743670641863569834115)
          ·
            refine ⟨3629615505962795354751173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419743670641863569834115 3629615505962795354751173)
            ·
              refine ⟨680552907368024129015845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3629615505962795354751173 680552907368024129015845)
              ·
                refine ⟨127603670131504524190471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680552907368024129015845 127603670131504524190471)
                ·
                  rfl

theorem cell20_838712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_838712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838712 prefixEnd_838712 := by exact prefixLift 838712
  have htrace : WordTrace (prefixWord ++ tailWord_838712) baseStart_838712 baseEnd_838712 := by
    simpa [prefixWord, tailWord_838712, baseEnd_838712] using wordTrace_append hprefix tailTrace_838712
  have hstable : (prefixWord ++ tailWord_838712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838712).length < 2 ^ (prefixWord ++ tailWord_838712).sum := by decide
  have hdescent : baseEnd_838712 < baseStart_838712 := by decide
  rcases family_descends (prefixWord ++ tailWord_838712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838749 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 3]
def baseStart_838749 : Nat := 118140960795 + 838749 * 2 ^ 59
def prefixEnd_838749 : Nat := 4983230072969 + 3 ^ 40 * 838749 * 2
def baseEnd_838749 : Nat := 382827898202705888337929

theorem tailTrace_838749 : CollatzResearch.WordTrace tailWord_838749 prefixEnd_838749 382827898202705888337929 := by
  unfold tailWord_838749
  simp only [CollatzResearch.WordTrace]
  refine ⟨30591689238363094769839301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20394459492242063179892867 30591689238363094769839301)
  ·
    refine ⟨5735941732193080269344869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30591689238363094769839301 5735941732193080269344869)
    ·
      refine ⟨1075489074786202550502163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5735941732193080269344869 1075489074786202550502163)
      ·
        refine ⟨1613233612179303825753245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075489074786202550502163 1613233612179303825753245)
        ·
          refine ⟨604962604567238934657467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1613233612179303825753245 604962604567238934657467)
          ·
            refine ⟨907443906850858401986201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604962604567238934657467 907443906850858401986201)
            ·
              refine ⟨680582930138143801489651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907443906850858401986201 680582930138143801489651)
              ·
                refine ⟨1020874395207215702234477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680582930138143801489651 1020874395207215702234477)
                ·
                  refine ⟨382827898202705888337929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020874395207215702234477 382827898202705888337929)
                  ·
                    rfl

theorem cell20_838749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_838749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838749 prefixEnd_838749 := by exact prefixLift 838749
  have htrace : WordTrace (prefixWord ++ tailWord_838749) baseStart_838749 baseEnd_838749 := by
    simpa [prefixWord, tailWord_838749, baseEnd_838749] using wordTrace_append hprefix tailTrace_838749
  have hstable : (prefixWord ++ tailWord_838749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838749).length < 2 ^ (prefixWord ++ tailWord_838749).sum := by decide
  have hdescent : baseEnd_838749 < baseStart_838749 := by decide
  rcases family_descends (prefixWord ++ tailWord_838749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838757 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_838757 : Nat := 118140960795 + 838757 * 2 ^ 59
def prefixEnd_838757 : Nat := 4983230072969 + 3 ^ 40 * 838757 * 2
def baseEnd_838757 : Nat := 382831549620693416071229

theorem tailTrace_838757 : CollatzResearch.WordTrace tailWord_838757 prefixEnd_838757 382831549620693416071229 := by
  unfold tailWord_838757
  simp only [CollatzResearch.WordTrace]
  refine ⟨30591981022334112136130525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20394654014889408090753683 30591981022334112136130525)
  ·
    refine ⟨11471992883375292051048947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30591981022334112136130525 11471992883375292051048947)
    ·
      refine ⟨17207989325062938076573421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11471992883375292051048947 17207989325062938076573421)
      ·
        refine ⟨6452995996898601778715033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17207989325062938076573421 6452995996898601778715033)
        ·
          refine ⟨4839746997673951334036275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6452995996898601778715033 4839746997673951334036275)
          ·
            refine ⟨7259620496510927001054413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839746997673951334036275 7259620496510927001054413)
            ·
              refine ⟨2722357686191597625395405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7259620496510927001054413 2722357686191597625395405)
              ·
                refine ⟨1020884132321849109523277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2722357686191597625395405 1020884132321849109523277)
                ·
                  refine ⟨382831549620693416071229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020884132321849109523277 382831549620693416071229)
                  ·
                    rfl

theorem cell20_838757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_838757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838757 prefixEnd_838757 := by exact prefixLift 838757
  have htrace : WordTrace (prefixWord ++ tailWord_838757) baseStart_838757 baseEnd_838757 := by
    simpa [prefixWord, tailWord_838757, baseEnd_838757] using wordTrace_append hprefix tailTrace_838757
  have hstable : (prefixWord ++ tailWord_838757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838757).length < 2 ^ (prefixWord ++ tailWord_838757).sum := by decide
  have hdescent : baseEnd_838757 < baseStart_838757 := by decide
  rcases family_descends (prefixWord ++ tailWord_838757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838781 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 2]
def baseStart_838781 : Nat := 118140960795 + 838781 * 2 ^ 59
def prefixEnd_838781 : Nat := 4983230072969 + 3 ^ 40 * 838781 * 2
def baseEnd_838781 : Nat := 382842503874655999271131

theorem tailTrace_838781 : CollatzResearch.WordTrace tailWord_838781 prefixEnd_838781 382842503874655999271131 := by
  unfold tailWord_838781
  simp only [CollatzResearch.WordTrace]
  refine ⟨30592856374247164235004197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20395237582831442823336131 30592856374247164235004197)
  ·
    refine ⟨5736160570171343294063287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30592856374247164235004197 5736160570171343294063287)
    ·
      refine ⟨8604240855257014941094931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736160570171343294063287 8604240855257014941094931)
      ·
        refine ⟨12906361282885522411642397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604240855257014941094931 12906361282885522411642397)
        ·
          refine ⟨4839885481082070904365899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12906361282885522411642397 4839885481082070904365899)
          ·
            refine ⟨7259828221623106356548849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839885481082070904365899 7259828221623106356548849)
            ·
              refine ⟨5444871166217329767411637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7259828221623106356548849 5444871166217329767411637)
              ·
                refine ⟨510456671832874665694841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5444871166217329767411637 510456671832874665694841)
                ·
                  refine ⟨382842503874655999271131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510456671832874665694841 382842503874655999271131)
                  ·
                    rfl

theorem cell20_838781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_838781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838781 prefixEnd_838781 := by exact prefixLift 838781
  have htrace : WordTrace (prefixWord ++ tailWord_838781) baseStart_838781 baseEnd_838781 := by
    simpa [prefixWord, tailWord_838781, baseEnd_838781] using wordTrace_append hprefix tailTrace_838781
  have hstable : (prefixWord ++ tailWord_838781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838781).length < 2 ^ (prefixWord ++ tailWord_838781).sum := by decide
  have hdescent : baseEnd_838781 < baseStart_838781 := by decide
  rcases family_descends (prefixWord ++ tailWord_838781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
