import V185TrunkScan22Chunk432

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3859708 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 4]
def baseStart_3859708 : Nat := 118140960795 + 3859708 * 2 ^ 59
def prefixEnd_3859708 : Nat := 4983230072969 + 3 ^ 40 * 3859708 * 2
def baseEnd_3859708 : Nat := 440418975556420024088785

theorem tailTrace_3859708 : CollatzResearch.WordTrace tailWord_3859708 prefixEnd_3859708 440418975556420024088785 := by
  unfold tailWord_3859708
  simp only [CollatzResearch.WordTrace]
  refine ⟨70387557950472288245529889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93850077267296384327373185 70387557950472288245529889)
  ·
    refine ⟨52790668462854216184147417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70387557950472288245529889 52790668462854216184147417)
    ·
      refine ⟨39593001347140662138110563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52790668462854216184147417 39593001347140662138110563)
      ·
        refine ⟨59389502020710993207165845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39593001347140662138110563 59389502020710993207165845)
        ·
          refine ⟨2783882907220827806585899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59389502020710993207165845 2783882907220827806585899)
          ·
            refine ⟨4175824360831241709878849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783882907220827806585899 4175824360831241709878849)
            ·
              refine ⟨3131868270623431282409137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4175824360831241709878849 3131868270623431282409137)
              ·
                refine ⟨2348901202967573461806853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131868270623431282409137 2348901202967573461806853)
                ·
                  refine ⟨440418975556420024088785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348901202967573461806853 440418975556420024088785)
                  ·
                    rfl

theorem cell22_3859708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_3859708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859708 prefixEnd_3859708 := by exact prefixLift 3859708
  have htrace : WordTrace (prefixWord ++ tailWord_3859708) baseStart_3859708 baseEnd_3859708 := by
    simpa [prefixWord, tailWord_3859708, baseEnd_3859708] using wordTrace_append hprefix tailTrace_3859708
  have hstable : (prefixWord ++ tailWord_3859708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859708).length < 2 ^ (prefixWord ++ tailWord_3859708).sum := by decide
  have hdescent : baseEnd_3859708 < baseStart_3859708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859715 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_3859715 : Nat := 118140960795 + 3859715 * 2 ^ 59
def prefixEnd_3859715 : Nat := 4983230072969 + 3 ^ 40 * 3859715 * 2
def baseEnd_3859715 : Nat := 1321259322912314387341333

theorem tailTrace_3859715 : CollatzResearch.WordTrace tailWord_3859715 prefixEnd_3859715 1321259322912314387341333 := by
  unfold tailWord_3859715
  simp only [CollatzResearch.WordTrace]
  refine ⟨140775371211919216686564599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93850247474612811124376399 140775371211919216686564599)
  ·
    refine ⟨211163056817878825029846899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140775371211919216686564599 211163056817878825029846899)
    ·
      refine ⟨316744585226818237544770349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211163056817878825029846899 316744585226818237544770349)
      ·
        refine ⟨118779219460056839079288881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316744585226818237544770349 118779219460056839079288881)
        ·
          refine ⟨89084414595042629309466661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118779219460056839079288881 89084414595042629309466661)
          ·
            refine ⟨16703327736570492995524999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89084414595042629309466661 16703327736570492995524999)
            ·
              refine ⟨25054991604855739493287499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16703327736570492995524999 25054991604855739493287499)
              ·
                refine ⟨37582487407283609239931249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25054991604855739493287499 37582487407283609239931249)
                ·
                  refine ⟨28186865555462706929948437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37582487407283609239931249 28186865555462706929948437)
                  ·
                    refine ⟨1321259322912314387341333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28186865555462706929948437 1321259322912314387341333)
                    ·
                      rfl

theorem cell22_3859715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_3859715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859715 prefixEnd_3859715 := by exact prefixLift 3859715
  have htrace : WordTrace (prefixWord ++ tailWord_3859715) baseStart_3859715 baseEnd_3859715 := by
    simpa [prefixWord, tailWord_3859715, baseEnd_3859715] using wordTrace_append hprefix tailTrace_3859715
  have hstable : (prefixWord ++ tailWord_3859715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859715).length < 2 ^ (prefixWord ++ tailWord_3859715).sum := by decide
  have hdescent : baseEnd_3859715 < baseStart_3859715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859717 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_3859717 : Nat := 118140960795 + 3859717 * 2 ^ 59
def prefixEnd_3859717 : Nat := 4983230072969 + 3 ^ 40 * 3859717 * 2
def baseEnd_3859717 : Nat := 1321260007553187048791327

theorem tailTrace_3859717 : CollatzResearch.WordTrace tailWord_3859717 prefixEnd_3859717 1321260007553187048791327 := by
  unfold tailWord_3859717
  simp only [CollatzResearch.WordTrace]
  refine ⟨140775444157911971028137405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93850296105274647352091603 140775444157911971028137405)
  ·
    refine ⟨52790791559216989135551527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140775444157911971028137405 52790791559216989135551527)
    ·
      refine ⟨79186187338825483703327291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52790791559216989135551527 79186187338825483703327291)
      ·
        refine ⟨118779281008238225554990937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79186187338825483703327291 118779281008238225554990937)
        ·
          refine ⟨89084460756178669166243203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118779281008238225554990937 89084460756178669166243203)
          ·
            refine ⟨133626691134268003749364805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89084460756178669166243203 133626691134268003749364805)
            ·
              refine ⟨25055004587675250703005901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133626691134268003749364805 25055004587675250703005901)
              ·
                refine ⟨9395626720378219013627213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25055004587675250703005901 9395626720378219013627213)
                ·
                  refine ⟨3523360020141832130110205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9395626720378219013627213 3523360020141832130110205)
                  ·
                    refine ⟨1321260007553187048791327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523360020141832130110205 1321260007553187048791327)
                    ·
                      rfl

theorem cell22_3859717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_3859717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859717 prefixEnd_3859717 := by exact prefixLift 3859717
  have htrace : WordTrace (prefixWord ++ tailWord_3859717) baseStart_3859717 baseEnd_3859717 := by
    simpa [prefixWord, tailWord_3859717, baseEnd_3859717] using wordTrace_append hprefix tailTrace_3859717
  have hstable : (prefixWord ++ tailWord_3859717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859717).length < 2 ^ (prefixWord ++ tailWord_3859717).sum := by decide
  have hdescent : baseEnd_3859717 < baseStart_3859717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859745 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3859745 : Nat := 118140960795 + 3859745 * 2 ^ 59
def prefixEnd_3859745 : Nat := 4983230072969 + 3 ^ 40 * 3859745 * 2
def baseEnd_3859745 : Nat := 1321269592525404309091241

theorem tailTrace_3859745 : CollatzResearch.WordTrace tailWord_3859745 prefixEnd_3859745 1321269592525404309091241 := by
  unfold tailWord_3859745
  simp only [CollatzResearch.WordTrace]
  refine ⟨140776465401810531810156689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93850976934540354540104459 140776465401810531810156689)
  ·
    refine ⟨105582349051357898857617517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140776465401810531810156689 105582349051357898857617517)
    ·
      refine ⟨39593380894259212071606569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105582349051357898857617517 39593380894259212071606569)
      ·
        refine ⟨29695035670694409053704927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39593380894259212071606569 29695035670694409053704927)
        ·
          refine ⟨44542553506041613580557391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29695035670694409053704927 44542553506041613580557391)
          ·
            refine ⟨66813830259062420370836087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44542553506041613580557391 66813830259062420370836087)
            ·
              refine ⟨100220745388593630556254131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66813830259062420370836087 100220745388593630556254131)
              ·
                refine ⟨150331118082890445834381197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100220745388593630556254131 150331118082890445834381197)
                ·
                  refine ⟨56374169281083917187892949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150331118082890445834381197 56374169281083917187892949)
                  ·
                    refine ⟨1321269592525404309091241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56374169281083917187892949 1321269592525404309091241)
                    ·
                      rfl

theorem cell22_3859745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3859745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859745 prefixEnd_3859745 := by exact prefixLift 3859745
  have htrace : WordTrace (prefixWord ++ tailWord_3859745) baseStart_3859745 baseEnd_3859745 := by
    simpa [prefixWord, tailWord_3859745, baseEnd_3859745] using wordTrace_append hprefix tailTrace_3859745
  have hstable : (prefixWord ++ tailWord_3859745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859745).length < 2 ^ (prefixWord ++ tailWord_3859745).sum := by decide
  have hdescent : baseEnd_3859745 < baseStart_3859745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859762 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3859762 : Nat := 118140960795 + 3859762 * 2 ^ 59
def prefixEnd_3859762 : Nat := 4983230072969 + 3 ^ 40 * 3859762 * 2
def baseEnd_3859762 : Nat := 1321275411972821931416189

theorem tailTrace_3859762 : CollatzResearch.WordTrace tailWord_3859762 prefixEnd_3859762 1321275411972821931416189 := by
  unfold tailWord_3859762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35194271360687235928381385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93851390295165962475683693 35194271360687235928381385)
  ·
    refine ⟨26395703520515426946286039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35194271360687235928381385 26395703520515426946286039)
    ·
      refine ⟨39593555280773140419429059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26395703520515426946286039 39593555280773140419429059)
      ·
        refine ⟨59390332921159710629143589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39593555280773140419429059 59390332921159710629143589)
        ·
          refine ⟨11135687422717445742964423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59390332921159710629143589 11135687422717445742964423)
          ·
            refine ⟨16703531134076168614446635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135687422717445742964423 16703531134076168614446635)
            ·
              refine ⟨25055296701114252921669953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16703531134076168614446635 25055296701114252921669953)
              ·
                refine ⟨18791472525835689691252465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25055296701114252921669953 18791472525835689691252465)
                ·
                  refine ⟨14093604394376767268439349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18791472525835689691252465 14093604394376767268439349)
                  ·
                    refine ⟨1321275411972821931416189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14093604394376767268439349 1321275411972821931416189)
                    ·
                      rfl

theorem cell22_3859762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3859762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859762 prefixEnd_3859762 := by exact prefixLift 3859762
  have htrace : WordTrace (prefixWord ++ tailWord_3859762) baseStart_3859762 baseEnd_3859762 := by
    simpa [prefixWord, tailWord_3859762, baseEnd_3859762] using wordTrace_append hprefix tailTrace_3859762
  have hstable : (prefixWord ++ tailWord_3859762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859762).length < 2 ^ (prefixWord ++ tailWord_3859762).sum := by decide
  have hdescent : baseEnd_3859762 < baseStart_3859762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859824 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_3859824 : Nat := 118140960795 + 3859824 * 2 ^ 59
def prefixEnd_3859824 : Nat := 4983230072969 + 3 ^ 40 * 3859824 * 2
def baseEnd_3859824 : Nat := 1321296635839874436365999

theorem tailTrace_3859824 : CollatzResearch.WordTrace tailWord_3859824 prefixEnd_3859824 1321296635839874436365999 := by
  unfold tailWord_3859824
  simp only [CollatzResearch.WordTrace]
  refine ⟨70389673384262164151141263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93852897845682885534855017 70389673384262164151141263)
  ·
    refine ⟨105584510076393246226711895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70389673384262164151141263 105584510076393246226711895)
    ·
      refine ⟨158376765114589869340067843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105584510076393246226711895 158376765114589869340067843)
      ·
        refine ⟨237565147671884804010101765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158376765114589869340067843 237565147671884804010101765)
        ·
          refine ⟨44543465188478400751894081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237565147671884804010101765 44543465188478400751894081)
          ·
            refine ⟨33407598891358800563920561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44543465188478400751894081 33407598891358800563920561)
            ·
              refine ⟨25055699168519100422940421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33407598891358800563920561 25055699168519100422940421)
              ·
                refine ⟨4697943594097331329301329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25055699168519100422940421 4697943594097331329301329)
                ·
                  refine ⟨3523457695572998496975997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697943594097331329301329 3523457695572998496975997)
                  ·
                    refine ⟨1321296635839874436365999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523457695572998496975997 1321296635839874436365999)
                    ·
                      rfl

theorem cell22_3859824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_3859824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859824 prefixEnd_3859824 := by exact prefixLift 3859824
  have htrace : WordTrace (prefixWord ++ tailWord_3859824) baseStart_3859824 baseEnd_3859824 := by
    simpa [prefixWord, tailWord_3859824, baseEnd_3859824] using wordTrace_append hprefix tailTrace_3859824
  have hstable : (prefixWord ++ tailWord_3859824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859824).length < 2 ^ (prefixWord ++ tailWord_3859824).sum := by decide
  have hdescent : baseEnd_3859824 < baseStart_3859824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859826 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_3859826 : Nat := 118140960795 + 3859826 * 2 ^ 59
def prefixEnd_3859826 : Nat := 4983230072969 + 3 ^ 40 * 3859826 * 2
def baseEnd_3859826 : Nat := 440432440160249032605331

theorem tailTrace_3859826 : CollatzResearch.WordTrace tailWord_3859826 prefixEnd_3859826 440432440160249032605331 := by
  unfold tailWord_3859826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35194854928629270660963833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93852946476344721762570221 35194854928629270660963833)
  ·
    refine ⟨26396141196471952995722875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35194854928629270660963833 26396141196471952995722875)
    ·
      refine ⟨39594211794707929493584313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26396141196471952995722875 39594211794707929493584313)
      ·
        refine ⟨29695658846030947120188235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39594211794707929493584313 29695658846030947120188235)
        ·
          refine ⟨44543488269046420680282353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29695658846030947120188235 44543488269046420680282353)
          ·
            refine ⟨33407616201784815510211765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44543488269046420680282353 33407616201784815510211765)
            ·
              refine ⟨3131964018917326454082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33407616201784815510211765 3131964018917326454082353)
              ·
                refine ⟨2348973014187994840561765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131964018917326454082353 2348973014187994840561765)
                ·
                  refine ⟨440432440160249032605331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348973014187994840561765 440432440160249032605331)
                  ·
                    rfl

theorem cell22_3859826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_3859826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859826 prefixEnd_3859826 := by exact prefixLift 3859826
  have htrace : WordTrace (prefixWord ++ tailWord_3859826) baseStart_3859826 baseEnd_3859826 := by
    simpa [prefixWord, tailWord_3859826, baseEnd_3859826] using wordTrace_append hprefix tailTrace_3859826
  have hstable : (prefixWord ++ tailWord_3859826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859826).length < 2 ^ (prefixWord ++ tailWord_3859826).sum := by decide
  have hdescent : baseEnd_3859826 < baseStart_3859826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859837 : List Nat := [1, 4, 1, 1, 2, 2, 4, 7]
def baseStart_3859837 : Nat := 118140960795 + 3859837 * 2 ^ 59
def prefixEnd_3859837 : Nat := 4983230072969 + 3 ^ 40 * 3859837 * 2
def baseEnd_3859837 : Nat := 146811231778394081754551

theorem tailTrace_3859837 : CollatzResearch.WordTrace tailWord_3859837 prefixEnd_3859837 146811231778394081754551 := by
  unfold tailWord_3859837
  simp only [CollatzResearch.WordTrace]
  refine ⟨140779820917477231522505765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93853213944984821015003843 140779820917477231522505765)
  ·
    refine ⟨26396216422026980910469831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140779820917477231522505765 26396216422026980910469831)
    ·
      refine ⟨39594324633040471365704747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26396216422026980910469831 39594324633040471365704747)
      ·
        refine ⟨59391486949560707048557121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39594324633040471365704747 59391486949560707048557121)
        ·
          refine ⟨44543615212170530286417841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59391486949560707048557121 44543615212170530286417841)
          ·
            refine ⟨33407711409127897714813381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44543615212170530286417841 33407711409127897714813381)
            ·
              refine ⟨6263945889211480821527509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33407711409127897714813381 6263945889211480821527509)
              ·
                refine ⟨146811231778394081754551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6263945889211480821527509 146811231778394081754551)
                ·
                  rfl

theorem cell22_3859837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 7].length) (baseStart_3859837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859837 prefixEnd_3859837 := by exact prefixLift 3859837
  have htrace : WordTrace (prefixWord ++ tailWord_3859837) baseStart_3859837 baseEnd_3859837 := by
    simpa [prefixWord, tailWord_3859837, baseEnd_3859837] using wordTrace_append hprefix tailTrace_3859837
  have hstable : (prefixWord ++ tailWord_3859837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859837).length < 2 ^ (prefixWord ++ tailWord_3859837).sum := by decide
  have hdescent : baseEnd_3859837 < baseStart_3859837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859944 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_3859944 : Nat := 118140960795 + 3859944 * 2 ^ 59
def prefixEnd_3859944 : Nat := 4983230072969 + 3 ^ 40 * 3859944 * 2
def baseEnd_3859944 : Nat := 440445904764078041121877

theorem tailTrace_3859944 : CollatzResearch.WordTrace tailWord_3859944 prefixEnd_3859944 440445904764078041121877 := by
  unfold tailWord_3859944
  simp only [CollatzResearch.WordTrace]
  refine ⟨70391861764044794398325443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93855815685393059197767257 70391861764044794398325443)
  ·
    refine ⟨105587792646067191597488165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70391861764044794398325443 105587792646067191597488165)
    ·
      refine ⟨19797711121137598424529031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105587792646067191597488165 19797711121137598424529031)
      ·
        refine ⟨29696566681706397636793547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19797711121137598424529031 29696566681706397636793547)
        ·
          refine ⟨44544850022559596455190321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29696566681706397636793547 44544850022559596455190321)
          ·
            refine ⟨33408637516919697341392741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44544850022559596455190321 33408637516919697341392741)
            ·
              refine ⟨6264119534422443251511139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33408637516919697341392741 6264119534422443251511139)
              ·
                refine ⟨9396179301633664877266709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264119534422443251511139 9396179301633664877266709)
                ·
                  refine ⟨440445904764078041121877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9396179301633664877266709 440445904764078041121877)
                  ·
                    rfl

theorem cell22_3859944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_3859944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859944 prefixEnd_3859944 := by exact prefixLift 3859944
  have htrace : WordTrace (prefixWord ++ tailWord_3859944) baseStart_3859944 baseEnd_3859944 := by
    simpa [prefixWord, tailWord_3859944, baseEnd_3859944] using wordTrace_append hprefix tailTrace_3859944
  have hstable : (prefixWord ++ tailWord_3859944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859944).length < 2 ^ (prefixWord ++ tailWord_3859944).sum := by decide
  have hdescent : baseEnd_3859944 < baseStart_3859944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859978 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_3859978 : Nat := 118140960795 + 3859978 * 2 ^ 59
def prefixEnd_3859978 : Nat := 4983230072969 + 3 ^ 40 * 3859978 * 2
def baseEnd_3859978 : Nat := 440449784395689789338509

theorem tailTrace_3859978 : CollatzResearch.WordTrace tailWord_3859978 prefixEnd_3859978 440449784395689789338509 := by
  unfold tailWord_3859978
  simp only [CollatzResearch.WordTrace]
  refine ⟨35196240902491603150847147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93856642406644275068925725 35196240902491603150847147)
  ·
    refine ⟨52794361353737404726270721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35196240902491603150847147 52794361353737404726270721)
    ·
      refine ⟨39595771015303053544703041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52794361353737404726270721 39595771015303053544703041)
      ·
        refine ⟨29696828261477290158527281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39595771015303053544703041 29696828261477290158527281)
        ·
          refine ⟨22272621196107967618895461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29696828261477290158527281 22272621196107967618895461)
          ·
            refine ⟨4176116474270243928542899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22272621196107967618895461 4176116474270243928542899)
            ·
              refine ⟨6264174711405365892814349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176116474270243928542899 6264174711405365892814349)
              ·
                refine ⟨2349065516777012209805381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6264174711405365892814349 2349065516777012209805381)
                ·
                  refine ⟨440449784395689789338509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2349065516777012209805381 440449784395689789338509)
                  ·
                    rfl

theorem cell22_3859978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_3859978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859978 prefixEnd_3859978 := by exact prefixLift 3859978
  have htrace : WordTrace (prefixWord ++ tailWord_3859978) baseStart_3859978 baseEnd_3859978 := by
    simpa [prefixWord, tailWord_3859978, baseEnd_3859978] using wordTrace_append hprefix tailTrace_3859978
  have hstable : (prefixWord ++ tailWord_3859978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859978).length < 2 ^ (prefixWord ++ tailWord_3859978).sum := by decide
  have hdescent : baseEnd_3859978 < baseStart_3859978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859989 : List Nat := [1, 3, 2, 1, 3, 4, 8]
def baseStart_3859989 : Nat := 118140960795 + 3859989 * 2 ^ 59
def prefixEnd_3859989 : Nat := 4983230072969 + 3 ^ 40 * 3859989 * 2
def baseEnd_3859989 : Nat := 48939004396735889110759

theorem tailTrace_3859989 : CollatzResearch.WordTrace tailWord_3859989 prefixEnd_3859989 48939004396735889110759 := by
  unfold tailWord_3859989
  simp only [CollatzResearch.WordTrace]
  refine ⟨140785364812926561482039021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93856909875284374321359347 140785364812926561482039021)
  ·
    refine ⟨52794511804847460555764633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140785364812926561482039021 52794511804847460555764633)
    ·
      refine ⟨39595883853635595416823475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52794511804847460555764633 39595883853635595416823475)
      ·
        refine ⟨59393825780453393125235213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39595883853635595416823475 59393825780453393125235213)
        ·
          refine ⟨22272684667670022421963205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59393825780453393125235213 22272684667670022421963205)
          ·
            refine ⟨4176128375188129204118101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22272684667670022421963205 4176128375188129204118101)
            ·
              refine ⟨48939004396735889110759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4176128375188129204118101 48939004396735889110759)
              ·
                rfl

theorem cell22_3859989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 8].length) (baseStart_3859989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3859989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3859989 prefixEnd_3859989 := by exact prefixLift 3859989
  have htrace : WordTrace (prefixWord ++ tailWord_3859989) baseStart_3859989 baseEnd_3859989 := by
    simpa [prefixWord, tailWord_3859989, baseEnd_3859989] using wordTrace_append hprefix tailTrace_3859989
  have hstable : (prefixWord ++ tailWord_3859989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859989).length < 2 ^ (prefixWord ++ tailWord_3859989).sum := by decide
  have hdescent : baseEnd_3859989 < baseStart_3859989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860049 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3860049 : Nat := 118140960795 + 3860049 * 2 ^ 59
def prefixEnd_3860049 : Nat := 4983230072969 + 3 ^ 40 * 3860049 * 2
def baseEnd_3860049 : Nat := 1321373657938048849490309

theorem tailTrace_3860049 : CollatzResearch.WordTrace tailWord_3860049 prefixEnd_3860049 1321373657938048849490309 := by
  unfold tailWord_3860049
  simp only [CollatzResearch.WordTrace]
  refine ⟨140787553192709191729223201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93858368795139461152815467 140787553192709191729223201)
  ·
    refine ⟨105590664894531893796917401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140787553192709191729223201 105590664894531893796917401)
    ·
      refine ⟨79192998670898920347688051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105590664894531893796917401 79192998670898920347688051)
      ·
        refine ⟨118789498006348380521532077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79192998670898920347688051 118789498006348380521532077)
        ·
          refine ⟨44546061752380642695574529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118789498006348380521532077 44546061752380642695574529)
          ·
            refine ⟨33409546314285482021680897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44546061752380642695574529 33409546314285482021680897)
            ·
              refine ⟨25057159735714111516260673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33409546314285482021680897 25057159735714111516260673)
              ·
                refine ⟨18792869801785583637195505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25057159735714111516260673 18792869801785583637195505)
                ·
                  refine ⟨14094652351339187727896629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18792869801785583637195505 14094652351339187727896629)
                  ·
                    refine ⟨1321373657938048849490309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14094652351339187727896629 1321373657938048849490309)
                    ·
                      rfl

theorem cell22_3860049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3860049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860049 prefixEnd_3860049 := by exact prefixLift 3860049
  have htrace : WordTrace (prefixWord ++ tailWord_3860049) baseStart_3860049 baseEnd_3860049 := by
    simpa [prefixWord, tailWord_3860049, baseEnd_3860049] using wordTrace_append hprefix tailTrace_3860049
  have hstable : (prefixWord ++ tailWord_3860049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860049).length < 2 ^ (prefixWord ++ tailWord_3860049).sum := by decide
  have hdescent : baseEnd_3860049 < baseStart_3860049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860055 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 1, 3]
def baseStart_3860055 : Nat := 118140960795 + 3860055 * 2 ^ 59
def prefixEnd_3860055 : Nat := 4983230072969 + 3 ^ 40 * 3860055 * 2
def baseEnd_3860055 : Nat := 1321375711860666833840291

theorem tailTrace_3860055 : CollatzResearch.WordTrace tailWord_3860055 prefixEnd_3860055 1321375711860666833840291 := by
  unfold tailWord_3860055
  simp only [CollatzResearch.WordTrace]
  refine ⟨140787772030687454753941619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93858514687124969835961079 140787772030687454753941619)
  ·
    refine ⟨211181658046031182130912429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140787772030687454753941619 211181658046031182130912429)
    ·
      refine ⟨79193121767261693299092161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211181658046031182130912429 79193121767261693299092161)
      ·
        refine ⟨59394841325446269974319121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79193121767261693299092161 59394841325446269974319121)
        ·
          refine ⟨44546130994084702480739341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59394841325446269974319121 44546130994084702480739341)
          ·
            refine ⟨16704799122781763430277253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44546130994084702480739341 16704799122781763430277253)
            ·
              refine ⟨3132149835521580643176985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16704799122781763430277253 3132149835521580643176985)
              ·
                refine ⟨2349112376641185482382739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132149835521580643176985 2349112376641185482382739)
                ·
                  refine ⟨3523668564961778223574109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349112376641185482382739 3523668564961778223574109)
                  ·
                    refine ⟨1321375711860666833840291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523668564961778223574109 1321375711860666833840291)
                    ·
                      rfl

theorem cell22_3860055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_3860055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860055 prefixEnd_3860055 := by exact prefixLift 3860055
  have htrace : WordTrace (prefixWord ++ tailWord_3860055) baseStart_3860055 baseEnd_3860055 := by
    simpa [prefixWord, tailWord_3860055, baseEnd_3860055] using wordTrace_append hprefix tailTrace_3860055
  have hstable : (prefixWord ++ tailWord_3860055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860055).length < 2 ^ (prefixWord ++ tailWord_3860055).sum := by decide
  have hdescent : baseEnd_3860055 < baseStart_3860055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860128 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_3860128 : Nat := 118140960795 + 3860128 * 2 ^ 59
def prefixEnd_3860128 : Nat := 4983230072969 + 3 ^ 40 * 3860128 * 2
def baseEnd_3860128 : Nat := 1321400701252518976765067

theorem tailTrace_3860128 : CollatzResearch.WordTrace tailWord_3860128 prefixEnd_3860128 1321400701252518976765067 := by
  unfold tailWord_3860128
  simp only [CollatzResearch.WordTrace]
  refine ⟨70395217279711494110674519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93860289706281992147566025 70395217279711494110674519)
  ·
    refine ⟨105592825919567241166011779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70395217279711494110674519 105592825919567241166011779)
    ·
      refine ⟨158389238879350861749017669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105592825919567241166011779 158389238879350861749017669)
      ·
        refine ⟨29697982289878286577940813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158389238879350861749017669 29697982289878286577940813)
        ·
          refine ⟨11136743358704357466727805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29697982289878286577940813 11136743358704357466727805)
          ·
            refine ⟨4176278759514134050022927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11136743358704357466727805 4176278759514134050022927)
            ·
              refine ⟨6264418139271201075034391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176278759514134050022927 6264418139271201075034391)
              ·
                refine ⟨9396627208906801612551587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264418139271201075034391 9396627208906801612551587)
                ·
                  refine ⟨14094940813360202418827381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396627208906801612551587 14094940813360202418827381)
                  ·
                    refine ⟨1321400701252518976765067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14094940813360202418827381 1321400701252518976765067)
                    ·
                      rfl

theorem cell22_3860128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_3860128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860128 prefixEnd_3860128 := by exact prefixLift 3860128
  have htrace : WordTrace (prefixWord ++ tailWord_3860128) baseStart_3860128 baseEnd_3860128 := by
    simpa [prefixWord, tailWord_3860128, baseEnd_3860128] using wordTrace_append hprefix tailTrace_3860128
  have hstable : (prefixWord ++ tailWord_3860128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860128).length < 2 ^ (prefixWord ++ tailWord_3860128).sum := by decide
  have hdescent : baseEnd_3860128 < baseStart_3860128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860141 : List Nat := [1, 5, 2, 1, 1, 1, 3, 8]
def baseStart_3860141 : Nat := 118140960795 + 3860141 * 2 ^ 59
def prefixEnd_3860141 : Nat := 4983230072969 + 3 ^ 40 * 3860141 * 2
def baseEnd_3860141 : Nat := 146822794602021252910003

theorem tailTrace_3860141 : CollatzResearch.WordTrace tailWord_3860141 prefixEnd_3860141 146822794602021252910003 := by
  unfold tailWord_3860141
  simp only [CollatzResearch.WordTrace]
  refine ⟨140790908708375891441572277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93860605805583927627714851 140790908708375891441572277)
  ·
    refine ⟨13199147691410239822647401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140790908708375891441572277 13199147691410239822647401)
    ·
      refine ⟨9899360768557679866985551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13199147691410239822647401 9899360768557679866985551)
      ·
        refine ⟨14849041152836519800478327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899360768557679866985551 14849041152836519800478327)
        ·
          refine ⟨22273561729254779700717491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14849041152836519800478327 22273561729254779700717491)
          ·
            refine ⟨33410342593882169551076237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22273561729254779700717491 33410342593882169551076237)
            ·
              refine ⟨12528878472705813581653589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33410342593882169551076237 12528878472705813581653589)
              ·
                refine ⟨146822794602021252910003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12528878472705813581653589 146822794602021252910003)
                ·
                  rfl

theorem cell22_3860141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 8].length) (baseStart_3860141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860141 prefixEnd_3860141 := by exact prefixLift 3860141
  have htrace : WordTrace (prefixWord ++ tailWord_3860141) baseStart_3860141 baseEnd_3860141 := by
    simpa [prefixWord, tailWord_3860141, baseEnd_3860141] using wordTrace_append hprefix tailTrace_3860141
  have hstable : (prefixWord ++ tailWord_3860141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860141).length < 2 ^ (prefixWord ++ tailWord_3860141).sum := by decide
  have hdescent : baseEnd_3860141 < baseStart_3860141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860280 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_3860280 : Nat := 118140960795 + 3860280 * 2 ^ 59
def prefixEnd_3860280 : Nat := 4983230072969 + 3 ^ 40 * 3860280 * 2
def baseEnd_3860280 : Nat := 1321452733958841246964601

theorem tailTrace_3860280 : CollatzResearch.WordTrace tailWord_3860280 prefixEnd_3860280 1321452733958841246964601 := by
  unfold tailWord_3860280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70397989227436159090441147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93863985636581545453921529 70397989227436159090441147)
  ·
    refine ⟨105596983841154238635661721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70397989227436159090441147 105596983841154238635661721)
    ·
      refine ⟨79197737880865678976746291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105596983841154238635661721 79197737880865678976746291)
      ·
        refine ⟨118796606821298518465119437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79197737880865678976746291 118796606821298518465119437)
        ·
          refine ⟨44548727557986944424419789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118796606821298518465119437 44548727557986944424419789)
          ·
            refine ⟨16705772834245104159157421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44548727557986944424419789 16705772834245104159157421)
            ·
              refine ⟨6264664812841914059684033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16705772834245104159157421 6264664812841914059684033)
              ·
                refine ⟨4698498609631435544763025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6264664812841914059684033 4698498609631435544763025)
                ·
                  refine ⟨3523873957223576658572269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698498609631435544763025 3523873957223576658572269)
                  ·
                    refine ⟨1321452733958841246964601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523873957223576658572269 1321452733958841246964601)
                    ·
                      rfl

theorem cell22_3860280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_3860280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860280 prefixEnd_3860280 := by exact prefixLift 3860280
  have htrace : WordTrace (prefixWord ++ tailWord_3860280) baseStart_3860280 baseEnd_3860280 := by
    simpa [prefixWord, tailWord_3860280, baseEnd_3860280] using wordTrace_append hprefix tailTrace_3860280
  have hstable : (prefixWord ++ tailWord_3860280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860280).length < 2 ^ (prefixWord ++ tailWord_3860280).sum := by decide
  have hdescent : baseEnd_3860280 < baseStart_3860280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860321 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 9]
def baseStart_3860321 : Nat := 118140960795 + 3860321 * 2 ^ 59
def prefixEnd_3860321 : Nat := 4983230072969 + 3 ^ 40 * 3860321 * 2
def baseEnd_3860321 : Nat := 440488923032243602229825

theorem tailTrace_3860321 : CollatzResearch.WordTrace tailWord_3860321 prefixEnd_3860321 440488923032243602229825 := by
  unfold tailWord_3860321
  simp only [CollatzResearch.WordTrace]
  refine ⟨140797473847723782183124817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93864982565149188122083211 140797473847723782183124817)
  ·
    refine ⟨105598105385792836637343613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140797473847723782183124817 105598105385792836637343613)
    ·
      refine ⟨39599289519672313739003855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105598105385792836637343613 39599289519672313739003855)
      ·
        refine ⟨59398934279508470608505783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39599289519672313739003855 59398934279508470608505783)
        ·
          refine ⟨89098401419262705912758675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59398934279508470608505783 89098401419262705912758675)
          ·
            refine ⟨133647602128894058869138013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89098401419262705912758675 133647602128894058869138013)
            ·
              refine ⟨50117850798335272075926755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133647602128894058869138013 50117850798335272075926755)
              ·
                refine ⟨75176776197502908113890133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50117850798335272075926755 75176776197502908113890133)
                ·
                  refine ⟨440488923032243602229825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75176776197502908113890133 440488923032243602229825)
                  ·
                    rfl

theorem cell22_3860321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_3860321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860321 prefixEnd_3860321 := by exact prefixLift 3860321
  have htrace : WordTrace (prefixWord ++ tailWord_3860321) baseStart_3860321 baseEnd_3860321 := by
    simpa [prefixWord, tailWord_3860321, baseEnd_3860321] using wordTrace_append hprefix tailTrace_3860321
  have hstable : (prefixWord ++ tailWord_3860321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860321).length < 2 ^ (prefixWord ++ tailWord_3860321).sum := by decide
  have hdescent : baseEnd_3860321 < baseStart_3860321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860338 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_3860338 : Nat := 118140960795 + 3860338 * 2 ^ 59
def prefixEnd_3860338 : Nat := 4983230072969 + 3 ^ 40 * 3860338 * 2
def baseEnd_3860338 : Nat := 440490862848049476338141

theorem tailTrace_3860338 : CollatzResearch.WordTrace tailWord_3860338 prefixEnd_3860338 440490862848049476338141 := by
  unfold tailWord_3860338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35199523472165548521623417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93865395925774796057662445 35199523472165548521623417)
  ·
    refine ⟨26399642604124161391217563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35199523472165548521623417 26399642604124161391217563)
    ·
      refine ⟨39599463906186242086826345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26399642604124161391217563 39599463906186242086826345)
      ·
        refine ⟨29699597929639681565119759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39599463906186242086826345 29699597929639681565119759)
        ·
          refine ⟨44549396894459522347679639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29699597929639681565119759 44549396894459522347679639)
          ·
            refine ⟨66824095341689283521519459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44549396894459522347679639 66824095341689283521519459)
            ·
              refine ⟨100236143012533925282279189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66824095341689283521519459 100236143012533925282279189)
              ·
                refine ⟨4698569203712527747606837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100236143012533925282279189 4698569203712527747606837)
                ·
                  refine ⟨440490862848049476338141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4698569203712527747606837 440490862848049476338141)
                  ·
                    rfl

theorem cell22_3860338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_3860338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860338 prefixEnd_3860338 := by exact prefixLift 3860338
  have htrace : WordTrace (prefixWord ++ tailWord_3860338) baseStart_3860338 baseEnd_3860338 := by
    simpa [prefixWord, tailWord_3860338, baseEnd_3860338] using wordTrace_append hprefix tailTrace_3860338
  have hstable : (prefixWord ++ tailWord_3860338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860338).length < 2 ^ (prefixWord ++ tailWord_3860338).sum := by decide
  have hdescent : baseEnd_3860338 < baseStart_3860338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860351 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_3860351 : Nat := 118140960795 + 3860351 * 2 ^ 59
def prefixEnd_3860351 : Nat := 4983230072969 + 3 ^ 40 * 3860351 * 2
def baseEnd_3860351 : Nat := 1321477038709820728439383

theorem tailTrace_3860351 : CollatzResearch.WordTrace tailWord_3860351 prefixEnd_3860351 1321477038709820728439383 := by
  unfold tailWord_3860351
  simp only [CollatzResearch.WordTrace]
  refine ⟨140798568037615097306716907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93865712025076731537811271 140798568037615097306716907)
  ·
    refine ⟨211197852056422645960075361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140798568037615097306716907 211197852056422645960075361)
    ·
      refine ⟨158398389042316984470056521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211197852056422645960075361 158398389042316984470056521)
      ·
        refine ⟨118798791781737738352542391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158398389042316984470056521 118798791781737738352542391)
        ·
          refine ⟨178198187672606607528813587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118798791781737738352542391 178198187672606607528813587)
          ·
            refine ⟨267297281508909911293220381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178198187672606607528813587 267297281508909911293220381)
            ·
              refine ⟨100236480565841216734957643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267297281508909911293220381 100236480565841216734957643)
              ·
                refine ⟨150354720848761825102436465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100236480565841216734957643 150354720848761825102436465)
                ·
                  refine ⟨112766040636571368826827349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150354720848761825102436465 112766040636571368826827349)
                  ·
                    refine ⟨1321477038709820728439383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112766040636571368826827349 1321477038709820728439383)
                    ·
                      rfl

theorem cell22_3860351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_3860351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860351 prefixEnd_3860351 := by exact prefixLift 3860351
  have htrace : WordTrace (prefixWord ++ tailWord_3860351) baseStart_3860351 baseEnd_3860351 := by
    simpa [prefixWord, tailWord_3860351, baseEnd_3860351] using wordTrace_append hprefix tailTrace_3860351
  have hstable : (prefixWord ++ tailWord_3860351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860351).length < 2 ^ (prefixWord ++ tailWord_3860351).sum := by decide
  have hdescent : baseEnd_3860351 < baseStart_3860351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860355 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 5]
def baseStart_3860355 : Nat := 118140960795 + 3860355 * 2 ^ 59
def prefixEnd_3860355 : Nat := 4983230072969 + 3 ^ 40 * 3860355 * 2
def baseEnd_3860355 : Nat := 440492802663855350446457

theorem tailTrace_3860355 : CollatzResearch.WordTrace tailWord_3860355 prefixEnd_3860355 440492802663855350446457 := by
  unfold tailWord_3860355
  simp only [CollatzResearch.WordTrace]
  refine ⟨140798713929600605989862519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93865809286400403993241679 140798713929600605989862519)
  ·
    refine ⟨211198070894400908984793779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140798713929600605989862519 211198070894400908984793779)
    ·
      refine ⟨316797106341601363477190669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211198070894400908984793779 316797106341601363477190669)
      ·
        refine ⟨118798914878100511303946501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316797106341601363477190669 118798914878100511303946501)
        ·
          refine ⟨22274796539643845869489969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118798914878100511303946501 22274796539643845869489969)
          ·
            refine ⟨16706097404732884402117477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22274796539643845869489969 16706097404732884402117477)
            ·
              refine ⟨3132393263387415825397027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16706097404732884402117477 3132393263387415825397027)
              ·
                refine ⟨4698589895081123738095541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132393263387415825397027 4698589895081123738095541)
                ·
                  refine ⟨440492802663855350446457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4698589895081123738095541 440492802663855350446457)
                  ·
                    rfl

theorem cell22_3860355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 5].length) (baseStart_3860355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860355 prefixEnd_3860355 := by exact prefixLift 3860355
  have htrace : WordTrace (prefixWord ++ tailWord_3860355) baseStart_3860355 baseEnd_3860355 := by
    simpa [prefixWord, tailWord_3860355, baseEnd_3860355] using wordTrace_append hprefix tailTrace_3860355
  have hstable : (prefixWord ++ tailWord_3860355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860355).length < 2 ^ (prefixWord ++ tailWord_3860355).sum := by decide
  have hdescent : baseEnd_3860355 < baseStart_3860355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860415 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 2, 3]
def baseStart_3860415 : Nat := 118140960795 + 3860415 * 2 ^ 59
def prefixEnd_3860415 : Nat := 4983230072969 + 3 ^ 40 * 3860415 * 2
def baseEnd_3860415 : Nat := 1321498947217745894839187

theorem tailTrace_3860415 : CollatzResearch.WordTrace tailWord_3860415 prefixEnd_3860415 1321498947217745894839187 := by
  unfold tailWord_3860415
  simp only [CollatzResearch.WordTrace]
  refine ⟨140800902309383236237046699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93867268206255490824697799 140800902309383236237046699)
  ·
    refine ⟨211201353464074854355570049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140800902309383236237046699 211201353464074854355570049)
    ·
      refine ⟨158401015098056140766677537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211201353464074854355570049 158401015098056140766677537)
      ·
        refine ⟨118800761323542105575008153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158401015098056140766677537 118800761323542105575008153)
        ·
          refine ⟨89100570992656579181256115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118800761323542105575008153 89100570992656579181256115)
          ·
            refine ⟨133650856488984868771884173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89100570992656579181256115 133650856488984868771884173)
            ·
              refine ⟨50119071183369325789456565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133650856488984868771884173 50119071183369325789456565)
              ·
                refine ⟨4698662923440874292761553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50119071183369325789456565 4698662923440874292761553)
                ·
                  refine ⟨3523997192580655719571165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698662923440874292761553 3523997192580655719571165)
                  ·
                    refine ⟨1321498947217745894839187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523997192580655719571165 1321498947217745894839187)
                    ·
                      rfl

theorem cell22_3860415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_3860415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860415 prefixEnd_3860415 := by exact prefixLift 3860415
  have htrace : WordTrace (prefixWord ++ tailWord_3860415) baseStart_3860415 baseEnd_3860415 := by
    simpa [prefixWord, tailWord_3860415, baseEnd_3860415] using wordTrace_append hprefix tailTrace_3860415
  have hstable : (prefixWord ++ tailWord_3860415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860415).length < 2 ^ (prefixWord ++ tailWord_3860415).sum := by decide
  have hdescent : baseEnd_3860415 < baseStart_3860415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860434 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3860434 : Nat := 118140960795 + 3860434 * 2 ^ 59
def prefixEnd_3860434 : Nat := 4983230072969 + 3 ^ 40 * 3860434 * 2
def baseEnd_3860434 : Nat := 440501817102012059538043

theorem tailTrace_3860434 : CollatzResearch.WordTrace tailWord_3860434 prefixEnd_3860434 440501817102012059538043 := by
  unfold tailWord_3860434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200398824078600620497089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93867730197542934987992237 35200398824078600620497089)
  ·
    refine ⟨26400299118058950465372817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35200398824078600620497089 26400299118058950465372817)
    ·
      refine ⟨19800224338544212849029613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26400299118058950465372817 19800224338544212849029613)
      ·
        refine ⟨7425084126954079818386105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19800224338544212849029613 7425084126954079818386105)
        ·
          refine ⟨5568813095215559863789579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425084126954079818386105 5568813095215559863789579)
          ·
            refine ⟨8353219642823339795684369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568813095215559863789579 8353219642823339795684369)
            ·
              refine ⟨6264914732117504846763277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8353219642823339795684369 6264914732117504846763277)
              ·
                refine ⟨2349343024544064317536229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6264914732117504846763277 2349343024544064317536229)
                ·
                  refine ⟨440501817102012059538043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2349343024544064317536229 440501817102012059538043)
                  ·
                    rfl

theorem cell22_3860434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3860434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860434 prefixEnd_3860434 := by exact prefixLift 3860434
  have htrace : WordTrace (prefixWord ++ tailWord_3860434) baseStart_3860434 baseEnd_3860434 := by
    simpa [prefixWord, tailWord_3860434, baseEnd_3860434] using wordTrace_append hprefix tailTrace_3860434
  have hstable : (prefixWord ++ tailWord_3860434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860434).length < 2 ^ (prefixWord ++ tailWord_3860434).sum := by decide
  have hdescent : baseEnd_3860434 < baseStart_3860434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860445 : List Nat := [1, 4, 3, 1, 3, 1, 9]
def baseStart_3860445 : Nat := 118140960795 + 3860445 * 2 ^ 59
def prefixEnd_3860445 : Nat := 4983230072969 + 3 ^ 40 * 3860445 * 2
def baseEnd_3860445 : Nat := 48944785808549474688485

theorem tailTrace_3860445 : CollatzResearch.WordTrace tailWord_3860445 prefixEnd_3860445 48944785808549474688485 := by
  unfold tailWord_3860445
  simp only [CollatzResearch.WordTrace]
  refine ⟨140801996499274551360638789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93867997666183034240425859 140801996499274551360638789)
  ·
    refine ⟨26400374343613978380119773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140801996499274551360638789 26400374343613978380119773)
    ·
      refine ⟨9900140378855241892544915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26400374343613978380119773 9900140378855241892544915)
      ·
        refine ⟨14850210568282862838817373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900140378855241892544915 14850210568282862838817373)
        ·
          refine ⟨5568828963106073564556515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14850210568282862838817373 5568828963106073564556515)
          ·
            refine ⟨8353243444659110346834773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568828963106073564556515 8353243444659110346834773)
            ·
              refine ⟨48944785808549474688485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8353243444659110346834773 48944785808549474688485)
              ·
                rfl

theorem cell22_3860445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 9].length) (baseStart_3860445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860445 prefixEnd_3860445 := by exact prefixLift 3860445
  have htrace : WordTrace (prefixWord ++ tailWord_3860445) baseStart_3860445 baseEnd_3860445 := by
    simpa [prefixWord, tailWord_3860445, baseEnd_3860445] using wordTrace_append hprefix tailTrace_3860445
  have hstable : (prefixWord ++ tailWord_3860445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860445).length < 2 ^ (prefixWord ++ tailWord_3860445).sum := by decide
  have hdescent : baseEnd_3860445 < baseStart_3860445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860537 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_3860537 : Nat := 118140960795 + 3860537 * 2 ^ 59
def prefixEnd_3860537 : Nat := 4983230072969 + 3 ^ 40 * 3860537 * 2
def baseEnd_3860537 : Nat := 1321540710310978243288813

theorem tailTrace_3860537 : CollatzResearch.WordTrace tailWord_3860537 prefixEnd_3860537 1321540710310978243288813 := by
  unfold tailWord_3860537
  simp only [CollatzResearch.WordTrace]
  refine ⟨140805352014941251072987865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93870234676627500715325243 140805352014941251072987865)
  ·
    refine ⟨105604014011205938304740899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140805352014941251072987865 105604014011205938304740899)
    ·
      refine ⟨158406021016808907457111349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105604014011205938304740899 158406021016808907457111349)
      ·
        refine ⟨14850564470325835074104189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158406021016808907457111349 14850564470325835074104189)
        ·
          refine ⟨5568961676372188152789071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14850564470325835074104189 5568961676372188152789071)
          ·
            refine ⟨8353442514558282229183607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568961676372188152789071 8353442514558282229183607)
            ·
              refine ⟨12530163771837423343775411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353442514558282229183607 12530163771837423343775411)
              ·
                refine ⟨18795245657756135015663117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530163771837423343775411 18795245657756135015663117)
                ·
                  refine ⟨7048217121658550630873669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18795245657756135015663117 7048217121658550630873669)
                  ·
                    refine ⟨1321540710310978243288813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7048217121658550630873669 1321540710310978243288813)
                    ·
                      rfl

theorem cell22_3860537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_3860537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860537 prefixEnd_3860537 := by exact prefixLift 3860537
  have htrace : WordTrace (prefixWord ++ tailWord_3860537) baseStart_3860537 baseEnd_3860537 := by
    simpa [prefixWord, tailWord_3860537, baseEnd_3860537] using wordTrace_append hprefix tailTrace_3860537
  have hstable : (prefixWord ++ tailWord_3860537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860537).length < 2 ^ (prefixWord ++ tailWord_3860537).sum := by decide
  have hdescent : baseEnd_3860537 < baseStart_3860537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860567 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 2, 3]
def baseStart_3860567 : Nat := 118140960795 + 3860567 * 2 ^ 59
def prefixEnd_3860567 : Nat := 4983230072969 + 3 ^ 40 * 3860567 * 2
def baseEnd_3860567 : Nat := 1321550979924068165038721

theorem tailTrace_3860567 : CollatzResearch.WordTrace tailWord_3860567 prefixEnd_3860567 1321550979924068165038721 := by
  unfold tailWord_3860567
  simp only [CollatzResearch.WordTrace]
  refine ⟨140806446204832566196579955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93870964136555044131053303 140806446204832566196579955)
  ·
    refine ⟨211209669307248849294869933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140806446204832566196579955 211209669307248849294869933)
    ·
      refine ⟨79203625990218318485576225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211209669307248849294869933 79203625990218318485576225)
      ·
        refine ⟨59402719492663738864182169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79203625990218318485576225 59402719492663738864182169)
        ·
          refine ⟨44552039619497804148136627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59402719492663738864182169 44552039619497804148136627)
          ·
            refine ⟨66828059429246706222204941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44552039619497804148136627 66828059429246706222204941)
            ·
              refine ⟨25060522285967514833326853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66828059429246706222204941 25060522285967514833326853)
              ·
                refine ⟨4698847928618909031248785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25060522285967514833326853 4698847928618909031248785)
                ·
                  refine ⟨3524135946464181773436589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698847928618909031248785 3524135946464181773436589)
                  ·
                    refine ⟨1321550979924068165038721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524135946464181773436589 1321550979924068165038721)
                    ·
                      rfl

theorem cell22_3860567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_3860567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860567 prefixEnd_3860567 := by exact prefixLift 3860567
  have htrace : WordTrace (prefixWord ++ tailWord_3860567) baseStart_3860567 baseEnd_3860567 := by
    simpa [prefixWord, tailWord_3860567, baseEnd_3860567] using wordTrace_append hprefix tailTrace_3860567
  have hstable : (prefixWord ++ tailWord_3860567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860567).length < 2 ^ (prefixWord ++ tailWord_3860567).sum := by decide
  have hdescent : baseEnd_3860567 < baseStart_3860567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860580 : List Nat := [2, 3, 1, 1, 2, 1, 5, 7]
def baseStart_3860580 : Nat := 118140960795 + 3860580 * 2 ^ 59
def prefixEnd_3860580 : Nat := 4983230072969 + 3 ^ 40 * 3860580 * 2
def baseEnd_3860580 : Nat := 146839492232193384940409

theorem tailTrace_3860580 : CollatzResearch.WordTrace tailWord_3860580 prefixEnd_3860580 146839492232193384940409 := by
  unfold tailWord_3860580
  simp only [CollatzResearch.WordTrace]
  refine ⟨70403460176892734708401597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93871280235856979611202129 70403460176892734708401597)
  ·
    refine ⟨26401297566334775515650599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70403460176892734708401597 26401297566334775515650599)
    ·
      refine ⟨39601946349502163273475899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26401297566334775515650599 39601946349502163273475899)
      ·
        refine ⟨59402919524253244910213849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39601946349502163273475899 59402919524253244910213849)
        ·
          refine ⟨44552189643189933682660387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59402919524253244910213849 44552189643189933682660387)
          ·
            refine ⟨66828284464784900523990581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44552189643189933682660387 66828284464784900523990581)
            ·
              refine ⟨6265151668573584424124117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66828284464784900523990581 6265151668573584424124117)
              ·
                refine ⟨146839492232193384940409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6265151668573584424124117 146839492232193384940409)
                ·
                  rfl

theorem cell22_3860580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_3860580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860580 prefixEnd_3860580 := by exact prefixLift 3860580
  have htrace : WordTrace (prefixWord ++ tailWord_3860580) baseStart_3860580 baseEnd_3860580 := by
    simpa [prefixWord, tailWord_3860580, baseEnd_3860580] using wordTrace_append hprefix tailTrace_3860580
  have hstable : (prefixWord ++ tailWord_3860580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860580).length < 2 ^ (prefixWord ++ tailWord_3860580).sum := by decide
  have hdescent : baseEnd_3860580 < baseStart_3860580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860612 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_3860612 : Nat := 118140960795 + 3860612 * 2 ^ 59
def prefixEnd_3860612 : Nat := 4983230072969 + 3 ^ 40 * 3860612 * 2
def baseEnd_3860612 : Nat := 1321566384343703047663583

theorem tailTrace_3860612 : CollatzResearch.WordTrace tailWord_3860612 prefixEnd_3860612 1321566384343703047663583 := by
  unfold tailWord_3860612
  simp only [CollatzResearch.WordTrace]
  refine ⟨70404043744834769440984045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93872058326446359254645393 70404043744834769440984045)
  ·
    refine ⟨26401516404313038540369017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70404043744834769440984045 26401516404313038540369017)
    ·
      refine ⟨19801137303234778905276763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26401516404313038540369017 19801137303234778905276763)
      ·
        refine ⟨29701705954852168357915145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19801137303234778905276763 29701705954852168357915145)
        ·
          refine ⟨22276279466139126268436359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29701705954852168357915145 22276279466139126268436359)
          ·
            refine ⟨33414419199208689402654539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22276279466139126268436359 33414419199208689402654539)
            ·
              refine ⟨50121628798813034103981809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33414419199208689402654539 50121628798813034103981809)
              ·
                refine ⟨37591221599109775577986357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50121628798813034103981809 37591221599109775577986357)
                ·
                  refine ⟨3524177024916541460436221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37591221599109775577986357 3524177024916541460436221)
                  ·
                    refine ⟨1321566384343703047663583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524177024916541460436221 1321566384343703047663583)
                    ·
                      rfl

theorem cell22_3860612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_3860612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860612 prefixEnd_3860612 := by exact prefixLift 3860612
  have htrace : WordTrace (prefixWord ++ tailWord_3860612) baseStart_3860612 baseEnd_3860612 := by
    simpa [prefixWord, tailWord_3860612, baseEnd_3860612] using wordTrace_append hprefix tailTrace_3860612
  have hstable : (prefixWord ++ tailWord_3860612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860612).length < 2 ^ (prefixWord ++ tailWord_3860612).sum := by decide
  have hdescent : baseEnd_3860612 < baseStart_3860612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860629 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3860629 : Nat := 118140960795 + 3860629 * 2 ^ 59
def prefixEnd_3860629 : Nat := 4983230072969 + 3 ^ 40 * 3860629 * 2
def baseEnd_3860629 : Nat := 1321572203791120669988531

theorem tailTrace_3860629 : CollatzResearch.WordTrace tailWord_3860629 prefixEnd_3860629 1321572203791120669988531 := by
  unfold tailWord_3860629
  simp only [CollatzResearch.WordTrace]
  refine ⟨140808707530607950785336941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93872471687071967190224627 140808707530607950785336941)
  ·
    refine ⟨52803265323977981544501353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140808707530607950785336941 52803265323977981544501353)
    ·
      refine ⟨39602448992983486158376015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52803265323977981544501353 39602448992983486158376015)
      ·
        refine ⟨59403673489475229237564023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39602448992983486158376015 59403673489475229237564023)
        ·
          refine ⟨89105510234212843856346035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59403673489475229237564023 89105510234212843856346035)
          ·
            refine ⟨133658265351319265784519053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89105510234212843856346035 133658265351319265784519053)
            ·
              refine ⟨50121849506744724669194645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133658265351319265784519053 50121849506744724669194645)
              ·
                refine ⟨2349461695628658968868499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50121849506744724669194645 2349461695628658968868499)
                ·
                  refine ⟨3524192543442988453302749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349461695628658968868499 3524192543442988453302749)
                  ·
                    refine ⟨1321572203791120669988531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524192543442988453302749 1321572203791120669988531)
                    ·
                      rfl

theorem cell22_3860629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3860629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860629 prefixEnd_3860629 := by exact prefixLift 3860629
  have htrace : WordTrace (prefixWord ++ tailWord_3860629) baseStart_3860629 baseEnd_3860629 := by
    simpa [prefixWord, tailWord_3860629, baseEnd_3860629] using wordTrace_append hprefix tailTrace_3860629
  have hstable : (prefixWord ++ tailWord_3860629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860629).length < 2 ^ (prefixWord ++ tailWord_3860629).sum := by decide
  have hdescent : baseEnd_3860629 < baseStart_3860629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860693 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 5]
def baseStart_3860693 : Nat := 118140960795 + 3860693 * 2 ^ 59
def prefixEnd_3860693 : Nat := 4983230072969 + 3 ^ 40 * 3860693 * 2
def baseEnd_3860693 : Nat := 440531370766348612129445

theorem tailTrace_3860693 : CollatzResearch.WordTrace tailWord_3860693 prefixEnd_3860693 440531370766348612129445 := by
  unfold tailWord_3860693
  simp only [CollatzResearch.WordTrace]
  refine ⟨140811041802376089715666733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93874027868250726477111155 140811041802376089715666733)
  ·
    refine ⟨52804140675891033643375025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140811041802376089715666733 52804140675891033643375025)
    ·
      refine ⟨39603105506918275232531269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52804140675891033643375025 39603105506918275232531269)
      ·
        refine ⟨7425582282547176606099613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39603105506918275232531269 7425582282547176606099613)
        ·
          refine ⟨2784593355955191227287355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7425582282547176606099613 2784593355955191227287355)
          ·
            refine ⟨4176890033932786840931033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784593355955191227287355 4176890033932786840931033)
            ·
              refine ⟨3132667525449590130698275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176890033932786840931033 3132667525449590130698275)
              ·
                refine ⟨4699001288174385196047413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132667525449590130698275 4699001288174385196047413)
                ·
                  refine ⟨440531370766348612129445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4699001288174385196047413 440531370766348612129445)
                  ·
                    rfl

theorem cell22_3860693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_3860693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860693 prefixEnd_3860693 := by exact prefixLift 3860693
  have htrace : WordTrace (prefixWord ++ tailWord_3860693) baseStart_3860693 baseEnd_3860693 := by
    simpa [prefixWord, tailWord_3860693, baseEnd_3860693] using wordTrace_append hprefix tailTrace_3860693
  have hstable : (prefixWord ++ tailWord_3860693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860693).length < 2 ^ (prefixWord ++ tailWord_3860693).sum := by decide
  have hdescent : baseEnd_3860693 < baseStart_3860693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860715 : List Nat := [1, 1, 1, 1, 2, 5, 1, 10]
def baseStart_3860715 : Nat := 118140960795 + 3860715 * 2 ^ 59
def prefixEnd_3860715 : Nat := 4983230072969 + 3 ^ 40 * 3860715 * 2
def baseEnd_3860715 : Nat := 146844627038738345815363

theorem tailTrace_3860715 : CollatzResearch.WordTrace tailWord_3860715 prefixEnd_3860715 146844627038738345815363 := by
  unfold tailWord_3860715
  simp only [CollatzResearch.WordTrace]
  refine ⟨140811844208296387472967599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93874562805530924981978399 140811844208296387472967599)
  ·
    refine ⟨211217766312444581209451399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140811844208296387472967599 211217766312444581209451399)
    ·
      refine ⟨316826649468666871814177099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211217766312444581209451399 316826649468666871814177099)
      ·
        refine ⟨475239974203000307721265649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316826649468666871814177099 475239974203000307721265649)
        ·
          refine ⟨356429980652250230790949237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475239974203000307721265649 356429980652250230790949237)
          ·
            refine ⟨33415310686148459136651491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356429980652250230790949237 33415310686148459136651491)
            ·
              refine ⟨50122966029222688704977237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33415310686148459136651491 50122966029222688704977237)
              ·
                refine ⟨146844627038738345815363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50122966029222688704977237 146844627038738345815363)
                ·
                  rfl

theorem cell22_3860715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 10].length) (baseStart_3860715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860715 prefixEnd_3860715 := by exact prefixLift 3860715
  have htrace : WordTrace (prefixWord ++ tailWord_3860715) baseStart_3860715 baseEnd_3860715 := by
    simpa [prefixWord, tailWord_3860715, baseEnd_3860715] using wordTrace_append hprefix tailTrace_3860715
  have hstable : (prefixWord ++ tailWord_3860715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860715).length < 2 ^ (prefixWord ++ tailWord_3860715).sum := by decide
  have hdescent : baseEnd_3860715 < baseStart_3860715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860734 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3860734 : Nat := 118140960795 + 3860734 * 2 ^ 59
def prefixEnd_3860734 : Nat := 4983230072969 + 3 ^ 40 * 3860734 * 2
def baseEnd_3860734 : Nat := 1321608147436935396113209

theorem tailTrace_3860734 : CollatzResearch.WordTrace tailWord_3860734 prefixEnd_3860734 1321608147436935396113209 := by
  unfold tailWord_3860734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17601567149403444214738657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93875024796818369145272837 17601567149403444214738657)
  ·
    refine ⟨13201175362052583161053993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17601567149403444214738657 13201175362052583161053993)
    ·
      refine ⟨9900881521539437370790495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13201175362052583161053993 9900881521539437370790495)
      ·
        refine ⟨14851322282309156056185743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900881521539437370790495 14851322282309156056185743)
        ·
          refine ⟨22276983423463734084278615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14851322282309156056185743 22276983423463734084278615)
          ·
            refine ⟨33415475135195601126417923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22276983423463734084278615 33415475135195601126417923)
            ·
              refine ⟨50123212702793401689626885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33415475135195601126417923 50123212702793401689626885)
              ·
                refine ⟨9398102381773762816805041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50123212702793401689626885 9398102381773762816805041)
                ·
                  refine ⟨7048576786330322112603781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9398102381773762816805041 7048576786330322112603781)
                  ·
                    refine ⟨1321608147436935396113209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7048576786330322112603781 1321608147436935396113209)
                    ·
                      rfl

theorem cell22_3860734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3860734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860734 prefixEnd_3860734 := by exact prefixLift 3860734
  have htrace : WordTrace (prefixWord ++ tailWord_3860734) baseStart_3860734 baseEnd_3860734 := by
    simpa [prefixWord, tailWord_3860734, baseEnd_3860734] using wordTrace_append hprefix tailTrace_3860734
  have hstable : (prefixWord ++ tailWord_3860734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860734).length < 2 ^ (prefixWord ++ tailWord_3860734).sum := by decide
  have hdescent : baseEnd_3860734 < baseStart_3860734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860738 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3860738 : Nat := 118140960795 + 3860738 * 2 ^ 59
def prefixEnd_3860738 : Nat := 4983230072969 + 3 ^ 40 * 3860738 * 2
def baseEnd_3860738 : Nat := 440536505572893573004399

theorem tailTrace_3860738 : CollatzResearch.WordTrace tailWord_3860738 prefixEnd_3860738 440536505572893573004399 := by
  unfold tailWord_3860738
  simp only [CollatzResearch.WordTrace]
  refine ⟨35203170771803265600263717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93875122058142041600703245 35203170771803265600263717)
  ·
    refine ⟨6600594519713112300049447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35203170771803265600263717 6600594519713112300049447)
    ·
      refine ⟨9900891779569668450074171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6600594519713112300049447 9900891779569668450074171)
      ·
        refine ⟨14851337669354502675111257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900891779569668450074171 14851337669354502675111257)
        ·
          refine ⟨11138503252015877006333443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14851337669354502675111257 11138503252015877006333443)
          ·
            refine ⟨16707754878023815509500165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11138503252015877006333443 16707754878023815509500165)
            ·
              refine ⟨3132704039629465408031281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16707754878023815509500165 3132704039629465408031281)
              ·
                refine ⟨2349528029722099056023461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132704039629465408031281 2349528029722099056023461)
                ·
                  refine ⟨440536505572893573004399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2349528029722099056023461 440536505572893573004399)
                  ·
                    rfl

theorem cell22_3860738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3860738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860738 prefixEnd_3860738 := by exact prefixLift 3860738
  have htrace : WordTrace (prefixWord ++ tailWord_3860738) baseStart_3860738 baseEnd_3860738 := by
    simpa [prefixWord, tailWord_3860738, baseEnd_3860738] using wordTrace_append hprefix tailTrace_3860738
  have hstable : (prefixWord ++ tailWord_3860738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860738).length < 2 ^ (prefixWord ++ tailWord_3860738).sum := by decide
  have hdescent : baseEnd_3860738 < baseStart_3860738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860792 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_3860792 : Nat := 118140960795 + 3860792 * 2 ^ 59
def prefixEnd_3860792 : Nat := 4983230072969 + 3 ^ 40 * 3860792 * 2
def baseEnd_3860792 : Nat := 1321628002022242578163031

theorem tailTrace_3860792 : CollatzResearch.WordTrace tailWord_3860792 prefixEnd_3860792 1321628002022242578163031 := by
  unfold tailWord_3860792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70407326314508714811760315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93876435086011619749013753 70407326314508714811760315)
  ·
    refine ⟨105610989471763072217640473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70407326314508714811760315 105610989471763072217640473)
    ·
      refine ⟨79208242103822304163230355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105610989471763072217640473 79208242103822304163230355)
      ·
        refine ⟨118812363155733456244845533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79208242103822304163230355 118812363155733456244845533)
        ·
          refine ⟨44554636183400046091817075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118812363155733456244845533 44554636183400046091817075)
          ·
            refine ⟨66831954275100069137725613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44554636183400046091817075 66831954275100069137725613)
            ·
              refine ⟨25061982853162525926647105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66831954275100069137725613 25061982853162525926647105)
              ·
                refine ⟨18796487139871894444985329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25061982853162525926647105 18796487139871894444985329)
                ·
                  refine ⟨14097365354903920833738997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18796487139871894444985329 14097365354903920833738997)
                  ·
                    refine ⟨1321628002022242578163031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14097365354903920833738997 1321628002022242578163031)
                    ·
                      rfl

theorem cell22_3860792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_3860792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860792 prefixEnd_3860792 := by exact prefixLift 3860792
  have htrace : WordTrace (prefixWord ++ tailWord_3860792) baseStart_3860792 baseEnd_3860792 := by
    simpa [prefixWord, tailWord_3860792, baseEnd_3860792] using wordTrace_append hprefix tailTrace_3860792
  have hstable : (prefixWord ++ tailWord_3860792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860792).length < 2 ^ (prefixWord ++ tailWord_3860792).sum := by decide
  have hdescent : baseEnd_3860792 < baseStart_3860792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860794 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_3860794 : Nat := 118140960795 + 3860794 * 2 ^ 59
def prefixEnd_3860794 : Nat := 4983230072969 + 3 ^ 40 * 3860794 * 2
def baseEnd_3860794 : Nat := 440542895554371746537675

theorem tailTrace_3860794 : CollatzResearch.WordTrace tailWord_3860794 prefixEnd_3860794 440542895554371746537675 := by
  unfold tailWord_3860794
  simp only [CollatzResearch.WordTrace]
  refine ⟨35203681393752545991273359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93876483716673455976728957 35203681393752545991273359)
  ·
    refine ⟨52805522090628818986910039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35203681393752545991273359 52805522090628818986910039)
    ·
      refine ⟨79208283135943228480365059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52805522090628818986910039 79208283135943228480365059)
      ·
        refine ⟨118812424703914842720547589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79208283135943228480365059 118812424703914842720547589)
        ·
          refine ⟨22277329631984033010102673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118812424703914842720547589 22277329631984033010102673)
          ·
            refine ⟨16707997223988024757577005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22277329631984033010102673 16707997223988024757577005)
            ·
              refine ⟨6265498958995509284091377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16707997223988024757577005 6265498958995509284091377)
              ·
                refine ⟨4699124219246631963068533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265498958995509284091377 4699124219246631963068533)
                ·
                  refine ⟨440542895554371746537675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4699124219246631963068533 440542895554371746537675)
                  ·
                    rfl

theorem cell22_3860794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_3860794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860794 prefixEnd_3860794 := by exact prefixLift 3860794
  have htrace : WordTrace (prefixWord ++ tailWord_3860794) baseStart_3860794 baseEnd_3860794 := by
    simpa [prefixWord, tailWord_3860794, baseEnd_3860794] using wordTrace_append hprefix tailTrace_3860794
  have hstable : (prefixWord ++ tailWord_3860794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860794).length < 2 ^ (prefixWord ++ tailWord_3860794).sum := by decide
  have hdescent : baseEnd_3860794 < baseStart_3860794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860798 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3860798 : Nat := 118140960795 + 3860798 * 2 ^ 59
def prefixEnd_3860798 : Nat := 4983230072969 + 3 ^ 40 * 3860798 * 2
def baseEnd_3860798 : Nat := 1321630055944860562513013

theorem tailTrace_3860798 : CollatzResearch.WordTrace tailWord_3860798 prefixEnd_3860798 1321630055944860562513013 := by
  unfold tailWord_3860798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17601858933374461581029881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93876580977997128432159365 17601858933374461581029881)
  ·
    refine ⟨13201394200030846185772411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17601858933374461581029881 13201394200030846185772411)
    ·
      refine ⟨19802091300046269278658617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201394200030846185772411 19802091300046269278658617)
      ·
        refine ⟨14851568475034701958993963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19802091300046269278658617 14851568475034701958993963)
        ·
          refine ⟨22277352712552052938490945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14851568475034701958993963 22277352712552052938490945)
          ·
            refine ⟨16708014534414039703868209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22277352712552052938490945 16708014534414039703868209)
            ·
              refine ⟨12531010900810529777901157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16708014534414039703868209 12531010900810529777901157)
              ·
                refine ⟨2349564543901974333356467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12531010900810529777901157 2349564543901974333356467)
                ·
                  refine ⟨3524346815852961500034701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349564543901974333356467 3524346815852961500034701)
                  ·
                    refine ⟨1321630055944860562513013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524346815852961500034701 1321630055944860562513013)
                    ·
                      rfl

theorem cell22_3860798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3860798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860798 prefixEnd_3860798 := by exact prefixLift 3860798
  have htrace : WordTrace (prefixWord ++ tailWord_3860798) baseStart_3860798 baseEnd_3860798 := by
    simpa [prefixWord, tailWord_3860798, baseEnd_3860798] using wordTrace_append hprefix tailTrace_3860798
  have hstable : (prefixWord ++ tailWord_3860798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860798).length < 2 ^ (prefixWord ++ tailWord_3860798).sum := by decide
  have hdescent : baseEnd_3860798 < baseStart_3860798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860871 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 2, 3]
def baseStart_3860871 : Nat := 118140960795 + 3860871 * 2 ^ 59
def prefixEnd_3860871 : Nat := 4983230072969 + 3 ^ 40 * 3860871 * 2
def baseEnd_3860871 : Nat := 1321655045336712705437789

theorem tailTrace_3860871 : CollatzResearch.WordTrace tailWord_3860871 prefixEnd_3860871 1321655045336712705437789 := by
  unfold tailWord_3860871
  simp only [CollatzResearch.WordTrace]
  refine ⟨140817533995731226115646467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93878355997154150743764311 140817533995731226115646467)
  ·
    refine ⟨211226300993596839173469701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140817533995731226115646467 211226300993596839173469701)
    ·
      refine ⟨39604931436299407345025569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211226300993596839173469701 39604931436299407345025569)
      ·
        refine ⟨29703698577224555508769177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39604931436299407345025569 29703698577224555508769177)
        ·
          refine ⟨22277773932918416631576883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29703698577224555508769177 22277773932918416631576883)
          ·
            refine ⟨33416660899377624947365325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22277773932918416631576883 33416660899377624947365325)
            ·
              refine ⟨12531247837266609355261997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33416660899377624947365325 12531247837266609355261997)
              ·
                refine ⟨4699217938974978508223249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12531247837266609355261997 4699217938974978508223249)
                ·
                  refine ⟨3524413454231233881167437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4699217938974978508223249 3524413454231233881167437)
                  ·
                    refine ⟨1321655045336712705437789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524413454231233881167437 1321655045336712705437789)
                    ·
                      rfl

theorem cell22_3860871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_3860871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860871 prefixEnd_3860871 := by exact prefixLift 3860871
  have htrace : WordTrace (prefixWord ++ tailWord_3860871) baseStart_3860871 baseEnd_3860871 := by
    simpa [prefixWord, tailWord_3860871, baseEnd_3860871] using wordTrace_append hprefix tailTrace_3860871
  have hstable : (prefixWord ++ tailWord_3860871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860871).length < 2 ^ (prefixWord ++ tailWord_3860871).sum := by decide
  have hdescent : baseEnd_3860871 < baseStart_3860871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860912 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_3860912 : Nat := 118140960795 + 3860912 * 2 ^ 59
def prefixEnd_3860912 : Nat := 4983230072969 + 3 ^ 40 * 3860912 * 2
def baseEnd_3860912 : Nat := 440556360158200755054221

theorem tailTrace_3860912 : CollatzResearch.WordTrace tailWord_3860912 prefixEnd_3860912 440556360158200755054221 := by
  unfold tailWord_3860912
  simp only [CollatzResearch.WordTrace]
  refine ⟨70409514694291345058944495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93879352925721793411925993 70409514694291345058944495)
  ·
    refine ⟨105614272041437017588416743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70409514694291345058944495 105614272041437017588416743)
    ·
      refine ⟨158421408062155526382625115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105614272041437017588416743 158421408062155526382625115)
      ·
        refine ⟨237632112093233289573937673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158421408062155526382625115 237632112093233289573937673)
        ·
          refine ⟨178224084069924967180453255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237632112093233289573937673 178224084069924967180453255)
          ·
            refine ⟨267336126104887450770679883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178224084069924967180453255 267336126104887450770679883)
            ·
              refine ⟨401004189157331176156019825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267336126104887450770679883 401004189157331176156019825)
              ·
                refine ⟨300753141867998382117014869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401004189157331176156019825 300753141867998382117014869)
                ·
                  refine ⟨440556360158200755054221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 300753141867998382117014869 440556360158200755054221)
                  ·
                    rfl

theorem cell22_3860912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_3860912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860912 prefixEnd_3860912 := by exact prefixLift 3860912
  have htrace : WordTrace (prefixWord ++ tailWord_3860912) baseStart_3860912 baseEnd_3860912 := by
    simpa [prefixWord, tailWord_3860912, baseEnd_3860912] using wordTrace_append hprefix tailTrace_3860912
  have hstable : (prefixWord ++ tailWord_3860912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860912).length < 2 ^ (prefixWord ++ tailWord_3860912).sum := by decide
  have hdescent : baseEnd_3860912 < baseStart_3860912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860963 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 5]
def baseStart_3860963 : Nat := 118140960795 + 3860963 * 2 ^ 59
def prefixEnd_3860963 : Nat := 4983230072969 + 3 ^ 40 * 3860963 * 2
def baseEnd_3860963 : Nat := 440562179605618377379169

theorem tailTrace_3860963 : CollatzResearch.WordTrace tailWord_3860963 prefixEnd_3860963 440562179605618377379169 := by
  unfold tailWord_3860963
  simp only [CollatzResearch.WordTrace]
  refine ⟨140820889511397925827995543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93880593007598617218663695 140820889511397925827995543)
  ·
    refine ⟨211231334267096888741993315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140820889511397925827995543 211231334267096888741993315)
    ·
      refine ⟨316847001400645333112989973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211231334267096888741993315 316847001400645333112989973)
      ·
        refine ⟨14852203190655249989671405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 316847001400645333112989973 14852203190655249989671405)
        ·
          refine ⟨5569576196495718746126777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14852203190655249989671405 5569576196495718746126777)
          ·
            refine ⟨4177182147371789059595083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5569576196495718746126777 4177182147371789059595083)
            ·
              refine ⟨6265773221057683589392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177182147371789059595083 6265773221057683589392625)
              ·
                refine ⟨4699329915793262692044469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265773221057683589392625 4699329915793262692044469)
                ·
                  refine ⟨440562179605618377379169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4699329915793262692044469 440562179605618377379169)
                  ·
                    rfl

theorem cell22_3860963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 5].length) (baseStart_3860963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860963 prefixEnd_3860963 := by exact prefixLift 3860963
  have htrace : WordTrace (prefixWord ++ tailWord_3860963) baseStart_3860963 baseEnd_3860963 := by
    simpa [prefixWord, tailWord_3860963, baseEnd_3860963] using wordTrace_append hprefix tailTrace_3860963
  have hstable : (prefixWord ++ tailWord_3860963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860963).length < 2 ^ (prefixWord ++ tailWord_3860963).sum := by decide
  have hdescent : baseEnd_3860963 < baseStart_3860963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860993 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3860993 : Nat := 118140960795 + 3860993 * 2 ^ 59
def prefixEnd_3860993 : Nat := 4983230072969 + 3 ^ 40 * 3860993 * 2
def baseEnd_3860993 : Nat := 1321696808429945053887415

theorem tailTrace_3860993 : CollatzResearch.WordTrace tailWord_3860993 prefixEnd_3860993 1321696808429945053887415 := by
  unfold tailWord_3860993
  simp only [CollatzResearch.WordTrace]
  refine ⟨140821983701289240951587633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93881322467526160634391755 140821983701289240951587633)
  ·
    refine ⟨105616487775966930713690725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140821983701289240951587633 105616487775966930713690725)
    ·
      refine ⟨19803091457993799508817011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105616487775966930713690725 19803091457993799508817011)
      ·
        refine ⟨29704637186990699263225517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19803091457993799508817011 29704637186990699263225517)
        ·
          refine ⟨11139238945121512223709569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29704637186990699263225517 11139238945121512223709569)
          ·
            refine ⟨8354429208841134167782177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11139238945121512223709569 8354429208841134167782177)
            ·
              refine ⟨6265821906630850625836633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8354429208841134167782177 6265821906630850625836633)
              ·
                refine ⟨4699366429973137969377475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265821906630850625836633 4699366429973137969377475)
                ·
                  refine ⟨7049049644959706954066213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699366429973137969377475 7049049644959706954066213)
                  ·
                    refine ⟨1321696808429945053887415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7049049644959706954066213 1321696808429945053887415)
                    ·
                      rfl

theorem cell22_3860993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3860993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3860993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3860993 prefixEnd_3860993 := by exact prefixLift 3860993
  have htrace : WordTrace (prefixWord ++ tailWord_3860993) baseStart_3860993 baseEnd_3860993 := by
    simpa [prefixWord, tailWord_3860993, baseEnd_3860993] using wordTrace_append hprefix tailTrace_3860993
  have hstable : (prefixWord ++ tailWord_3860993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860993).length < 2 ^ (prefixWord ++ tailWord_3860993).sum := by decide
  have hdescent : baseEnd_3860993 < baseStart_3860993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861021 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3861021 : Nat := 118140960795 + 3861021 * 2 ^ 59
def prefixEnd_3861021 : Nat := 4983230072969 + 3 ^ 40 * 3861021 * 2
def baseEnd_3861021 : Nat := 1321706393402162314187329

theorem tailTrace_3861021 : CollatzResearch.WordTrace tailWord_3861021 prefixEnd_3861021 1321706393402162314187329 := by
  unfold tailWord_3861021
  simp only [CollatzResearch.WordTrace]
  refine ⟨140823004945187801733606917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93882003296791867822404611 140823004945187801733606917)
  ·
    refine ⟨26404313427222712825051297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140823004945187801733606917 26404313427222712825051297)
    ·
      refine ⟨19803235070417034618788473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26404313427222712825051297 19803235070417034618788473)
      ·
        refine ⟨14852426302812775964091355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19803235070417034618788473 14852426302812775964091355)
        ·
          refine ⟨22278639454219163946137033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14852426302812775964091355 22278639454219163946137033)
          ·
            refine ⟨16708979590664372959602775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22278639454219163946137033 16708979590664372959602775)
            ·
              refine ⟨25063469385996559439404163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16708979590664372959602775 25063469385996559439404163)
              ·
                refine ⟨37595204078994839159106245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25063469385996559439404163 37595204078994839159106245)
                ·
                  refine ⟨7049100764811532342332421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37595204078994839159106245 7049100764811532342332421)
                  ·
                    refine ⟨1321706393402162314187329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7049100764811532342332421 1321706393402162314187329)
                    ·
                      rfl

theorem cell22_3861021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3861021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861021 prefixEnd_3861021 := by exact prefixLift 3861021
  have htrace : WordTrace (prefixWord ++ tailWord_3861021) baseStart_3861021 baseEnd_3861021 := by
    simpa [prefixWord, tailWord_3861021, baseEnd_3861021] using wordTrace_append hprefix tailTrace_3861021
  have hstable : (prefixWord ++ tailWord_3861021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861021).length < 2 ^ (prefixWord ++ tailWord_3861021).sum := by decide
  have hdescent : baseEnd_3861021 < baseStart_3861021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861044 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_3861044 : Nat := 118140960795 + 3861044 * 2 ^ 59
def prefixEnd_3861044 : Nat := 4983230072969 + 3 ^ 40 * 3861044 * 2
def baseEnd_3861044 : Nat := 1321714266772197920862259

theorem tailTrace_3861044 : CollatzResearch.WordTrace tailWord_3861044 prefixEnd_3861044 1321714266772197920862259 := by
  unfold tailWord_3861044
  simp only [CollatzResearch.WordTrace]
  refine ⟨70411921912052238330847093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93882562549402984441129457 70411921912052238330847093)
  ·
    refine ⟨6601117679254897343516915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70411921912052238330847093 6601117679254897343516915)
    ·
      refine ⟨9901676518882346015275373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601117679254897343516915 9901676518882346015275373)
      ·
        refine ⟨3713128694580879755728265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9901676518882346015275373 3713128694580879755728265)
        ·
          refine ⟨2784846520935659816796199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3713128694580879755728265 2784846520935659816796199)
          ·
            refine ⟨4177269781403489725194299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784846520935659816796199 4177269781403489725194299)
            ·
              refine ⟨6265904672105234587791449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177269781403489725194299 6265904672105234587791449)
              ·
                refine ⟨4699428504078925940843587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265904672105234587791449 4699428504078925940843587)
                ·
                  refine ⟨7049142756118388911265381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699428504078925940843587 7049142756118388911265381)
                  ·
                    refine ⟨1321714266772197920862259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7049142756118388911265381 1321714266772197920862259)
                    ·
                      rfl

theorem cell22_3861044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_3861044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861044 prefixEnd_3861044 := by exact prefixLift 3861044
  have htrace : WordTrace (prefixWord ++ tailWord_3861044) baseStart_3861044 baseEnd_3861044 := by
    simpa [prefixWord, tailWord_3861044, baseEnd_3861044] using wordTrace_append hprefix tailTrace_3861044
  have hstable : (prefixWord ++ tailWord_3861044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861044).length < 2 ^ (prefixWord ++ tailWord_3861044).sum := by decide
  have hdescent : baseEnd_3861044 < baseStart_3861044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861064 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_3861064 : Nat := 118140960795 + 3861064 * 2 ^ 59
def prefixEnd_3861064 : Nat := 4983230072969 + 3 ^ 40 * 3861064 * 2
def baseEnd_3861064 : Nat := 440573704393641511787399

theorem tailTrace_3861064 : CollatzResearch.WordTrace tailWord_3861064 prefixEnd_3861064 440573704393641511787399 := by
  unfold tailWord_3861064
  simp only [CollatzResearch.WordTrace]
  refine ⟨70412286642016010038711123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93883048856021346718281497 70412286642016010038711123)
  ·
    refine ⟨105618429963024015058066685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70412286642016010038711123 105618429963024015058066685)
    ·
      refine ⟨39606911236134005646775007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105618429963024015058066685 39606911236134005646775007)
      ·
        refine ⟨59410366854201008470162511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39606911236134005646775007 59410366854201008470162511)
        ·
          refine ⟨89115550281301512705243767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59410366854201008470162511 89115550281301512705243767)
          ·
            refine ⟨133673325421952269057865651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89115550281301512705243767 133673325421952269057865651)
            ·
              refine ⟨200509988132928403586798477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133673325421952269057865651 200509988132928403586798477)
              ·
                refine ⟨75191245549848151345049429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200509988132928403586798477 75191245549848151345049429)
                ·
                  refine ⟨440573704393641511787399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75191245549848151345049429 440573704393641511787399)
                  ·
                    rfl

theorem cell22_3861064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_3861064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861064 prefixEnd_3861064 := by exact prefixLift 3861064
  have htrace : WordTrace (prefixWord ++ tailWord_3861064) baseStart_3861064 baseEnd_3861064 := by
    simpa [prefixWord, tailWord_3861064, baseEnd_3861064] using wordTrace_append hprefix tailTrace_3861064
  have hstable : (prefixWord ++ tailWord_3861064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861064).length < 2 ^ (prefixWord ++ tailWord_3861064).sum := by decide
  have hdescent : baseEnd_3861064 < baseStart_3861064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861111 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 3, 4]
def baseStart_3861111 : Nat := 118140960795 + 3861111 * 2 ^ 59
def prefixEnd_3861111 : Nat := 4983230072969 + 3 ^ 40 * 3861111 * 2
def baseEnd_3861111 : Nat := 1321737202241432079437053

theorem tailTrace_3861111 : CollatzResearch.WordTrace tailWord_3861111 prefixEnd_3861111 1321737202241432079437053 := by
  unfold tailWord_3861111
  simp only [CollatzResearch.WordTrace]
  refine ⟨140826287514861747104383187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93884191676574498069588791 140826287514861747104383187)
  ·
    refine ⟨211239431272292620656574781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140826287514861747104383187 211239431272292620656574781)
    ·
      refine ⟨79214786727109732746215543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211239431272292620656574781 79214786727109732746215543)
      ·
        refine ⟨118822180090664599119323315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79214786727109732746215543 118822180090664599119323315)
        ·
          refine ⟨178233270135996898678984973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118822180090664599119323315 178233270135996898678984973)
          ·
            refine ⟨66837476300998837004619365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178233270135996898678984973 66837476300998837004619365)
            ·
              refine ⟨12532026806437281938366131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66837476300998837004619365 12532026806437281938366131)
              ·
                refine ⟨18798040209655922907549197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12532026806437281938366131 18798040209655922907549197)
                ·
                  refine ⟨7049265078620971090330949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18798040209655922907549197 7049265078620971090330949)
                  ·
                    refine ⟨1321737202241432079437053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7049265078620971090330949 1321737202241432079437053)
                    ·
                      rfl

theorem cell22_3861111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_3861111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861111 prefixEnd_3861111 := by exact prefixLift 3861111
  have htrace : WordTrace (prefixWord ++ tailWord_3861111) baseStart_3861111 baseEnd_3861111 := by
    simpa [prefixWord, tailWord_3861111, baseEnd_3861111] using wordTrace_append hprefix tailTrace_3861111
  have hstable : (prefixWord ++ tailWord_3861111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861111).length < 2 ^ (prefixWord ++ tailWord_3861111).sum := by decide
  have hdescent : baseEnd_3861111 < baseStart_3861111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861143 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 4]
def baseStart_3861143 : Nat := 118140960795 + 3861143 * 2 ^ 59
def prefixEnd_3861143 : Nat := 4983230072969 + 3 ^ 40 * 3861143 * 2
def baseEnd_3861143 : Nat := 440582718831798220878985

theorem tailTrace_3861143 : CollatzResearch.WordTrace tailWord_3861143 prefixEnd_3861143 440582718831798220878985 := by
  unfold tailWord_3861143
  simp only [CollatzResearch.WordTrace]
  refine ⟨140827454650745816569548083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93884969767163877713032055 140827454650745816569548083)
  ·
    refine ⟨211241181976118724854322125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140827454650745816569548083 211241181976118724854322125)
    ·
      refine ⟨79215443241044521820370797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211241181976118724854322125 79215443241044521820370797)
      ·
        refine ⟨29705791215391695682639049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79215443241044521820370797 29705791215391695682639049)
        ·
          refine ⟨22279343411543771761979287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29705791215391695682639049 22279343411543771761979287)
          ·
            refine ⟨33419015117315657642968931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22279343411543771761979287 33419015117315657642968931)
            ·
              refine ⟨50128522675973486464453397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33419015117315657642968931 50128522675973486464453397)
              ·
                refine ⟨2349774500436257178021253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50128522675973486464453397 2349774500436257178021253)
                ·
                  refine ⟨440582718831798220878985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2349774500436257178021253 440582718831798220878985)
                  ·
                    rfl

theorem cell22_3861143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 4].length) (baseStart_3861143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861143 prefixEnd_3861143 := by exact prefixLift 3861143
  have htrace : WordTrace (prefixWord ++ tailWord_3861143) baseStart_3861143 baseEnd_3861143 := by
    simpa [prefixWord, tailWord_3861143, baseEnd_3861143] using wordTrace_append hprefix tailTrace_3861143
  have hstable : (prefixWord ++ tailWord_3861143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861143).length < 2 ^ (prefixWord ++ tailWord_3861143).sum := by decide
  have hdescent : baseEnd_3861143 < baseStart_3861143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861156 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3861156 : Nat := 118140960795 + 3861156 * 2 ^ 59
def prefixEnd_3861156 : Nat := 4983230072969 + 3 ^ 40 * 3861156 * 2
def baseEnd_3861156 : Nat := 1321752606661066962061915

theorem tailTrace_3861156 : CollatzResearch.WordTrace tailWord_3861156 prefixEnd_3861156 1321752606661066962061915 := by
  unfold tailWord_3861156
  simp only [CollatzResearch.WordTrace]
  refine ⟨70413964399849359894885661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93885285866465813193180881 70413964399849359894885661)
  ·
    refine ⟨26405236649943509960582123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70413964399849359894885661 26405236649943509960582123)
    ·
      refine ⟨39607854974915264940873185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26405236649943509960582123 39607854974915264940873185)
      ·
        refine ⟨29705891231186448705654889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39607854974915264940873185 29705891231186448705654889)
        ·
          refine ⟨22279418423389836529241167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29705891231186448705654889 22279418423389836529241167)
          ·
            refine ⟨33419127635084754793861751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22279418423389836529241167 33419127635084754793861751)
            ·
              refine ⟨50128691452627132190792627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33419127635084754793861751 50128691452627132190792627)
              ·
                refine ⟨75193037178940698286188941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50128691452627132190792627 75193037178940698286188941)
                ·
                  refine ⟨28197388942102761857320853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75193037178940698286188941 28197388942102761857320853)
                  ·
                    refine ⟨1321752606661066962061915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28197388942102761857320853 1321752606661066962061915)
                    ·
                      rfl

theorem cell22_3861156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3861156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861156 prefixEnd_3861156 := by exact prefixLift 3861156
  have htrace : WordTrace (prefixWord ++ tailWord_3861156) baseStart_3861156 baseEnd_3861156 := by
    simpa [prefixWord, tailWord_3861156, baseEnd_3861156] using wordTrace_append hprefix tailTrace_3861156
  have hstable : (prefixWord ++ tailWord_3861156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861156).length < 2 ^ (prefixWord ++ tailWord_3861156).sum := by decide
  have hdescent : baseEnd_3861156 < baseStart_3861156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861171 : List Nat := [1, 1, 1, 2, 3, 5, 1, 8]
def baseStart_3861171 : Nat := 118140960795 + 3861171 * 2 ^ 59
def prefixEnd_3861171 : Nat := 4983230072969 + 3 ^ 40 * 3861171 * 2
def baseEnd_3861171 : Nat := 146861971274179102548541

theorem tailTrace_3861171 : CollatzResearch.WordTrace tailWord_3861171 prefixEnd_3861171 146861971274179102548541 := by
  unfold tailWord_3861171
  simp only [CollatzResearch.WordTrace]
  refine ⟨140828475894644377351567367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93885650596429584901044911 140828475894644377351567367)
  ·
    refine ⟨211242713841966566027351051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140828475894644377351567367 211242713841966566027351051)
    ·
      refine ⟨316864070762949849041026577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211242713841966566027351051 316864070762949849041026577)
      ·
        refine ⟨237648053072212386780769933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316864070762949849041026577 237648053072212386780769933)
        ·
          refine ⟨89118019902079645042788725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237648053072212386780769933 89118019902079645042788725)
          ·
            refine ⟨8354814365819966722761443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89118019902079645042788725 8354814365819966722761443)
            ·
              refine ⟨12532221548729950084142165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354814365819966722761443 12532221548729950084142165)
              ·
                refine ⟨146861971274179102548541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12532221548729950084142165 146861971274179102548541)
                ·
                  rfl

theorem cell22_3861171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 8].length) (baseStart_3861171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861171 prefixEnd_3861171 := by exact prefixLift 3861171
  have htrace : WordTrace (prefixWord ++ tailWord_3861171) baseStart_3861171 baseEnd_3861171 := by
    simpa [prefixWord, tailWord_3861171, baseEnd_3861171] using wordTrace_append hprefix tailTrace_3861171
  have hstable : (prefixWord ++ tailWord_3861171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861171).length < 2 ^ (prefixWord ++ tailWord_3861171).sum := by decide
  have hdescent : baseEnd_3861171 < baseStart_3861171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861173 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3861173 : Nat := 118140960795 + 3861173 * 2 ^ 59
def prefixEnd_3861173 : Nat := 4983230072969 + 3 ^ 40 * 3861173 * 2
def baseEnd_3861173 : Nat := 1321758426108484584386863

theorem tailTrace_3861173 : CollatzResearch.WordTrace tailWord_3861173 prefixEnd_3861173 1321758426108484584386863 := by
  unfold tailWord_3861173
  simp only [CollatzResearch.WordTrace]
  refine ⟨140828548840637131693140173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93885699227091421128760115 140828548840637131693140173)
  ·
    refine ⟨52810705815238924384927565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140828548840637131693140173 52810705815238924384927565)
    ·
      refine ⟨19804014680714596644347837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52810705815238924384927565 19804014680714596644347837)
      ·
        refine ⟨7426505505267973741630439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19804014680714596644347837 7426505505267973741630439)
        ·
          refine ⟨11139758257901960612445659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426505505267973741630439 11139758257901960612445659)
          ·
            refine ⟨16709637386852940918668489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139758257901960612445659 16709637386852940918668489)
            ·
              refine ⟨12532228040139705689001367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16709637386852940918668489 12532228040139705689001367)
              ·
                refine ⟨18798342060209558533502051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12532228040139705689001367 18798342060209558533502051)
                ·
                  refine ⟨28197513090314337800253077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18798342060209558533502051 28197513090314337800253077)
                  ·
                    refine ⟨1321758426108484584386863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28197513090314337800253077 1321758426108484584386863)
                    ·
                      rfl

theorem cell22_3861173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3861173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861173 prefixEnd_3861173 := by exact prefixLift 3861173
  have htrace : WordTrace (prefixWord ++ tailWord_3861173) baseStart_3861173 baseEnd_3861173 := by
    simpa [prefixWord, tailWord_3861173, baseEnd_3861173] using wordTrace_append hprefix tailTrace_3861173
  have hstable : (prefixWord ++ tailWord_3861173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861173).length < 2 ^ (prefixWord ++ tailWord_3861173).sum := by decide
  have hdescent : baseEnd_3861173 < baseStart_3861173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861188 : List Nat := [2, 3, 3, 1, 1, 4, 8]
def baseStart_3861188 : Nat := 118140960795 + 3861188 * 2 ^ 59
def prefixEnd_3861188 : Nat := 4983230072969 + 3 ^ 40 * 3861188 * 2
def baseEnd_3861188 : Nat := 48954205959815909083771

theorem tailTrace_3861188 : CollatzResearch.WordTrace tailWord_3861188 prefixEnd_3861188 48954205959815909083771 := by
  unfold tailWord_3861188
  simp only [CollatzResearch.WordTrace]
  refine ⟨70414547967791394627468109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93886063957055192836624145 70414547967791394627468109)
  ·
    refine ⟨26405455487921772985300541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70414547967791394627468109 26405455487921772985300541)
    ·
      refine ⟨9902045807970664869487703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26405455487921772985300541 9902045807970664869487703)
      ·
        refine ⟨14853068711955997304231555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9902045807970664869487703 14853068711955997304231555)
        ·
          refine ⟨22279603067933995956347333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14853068711955997304231555 22279603067933995956347333)
          ·
            refine ⟨4177425575237624241815125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22279603067933995956347333 4177425575237624241815125)
            ·
              refine ⟨48954205959815909083771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4177425575237624241815125 48954205959815909083771)
              ·
                rfl

theorem cell22_3861188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 8].length) (baseStart_3861188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861188 prefixEnd_3861188 := by exact prefixLift 3861188
  have htrace : WordTrace (prefixWord ++ tailWord_3861188) baseStart_3861188 baseEnd_3861188 := by
    simpa [prefixWord, tailWord_3861188, baseEnd_3861188] using wordTrace_append hprefix tailTrace_3861188
  have hstable : (prefixWord ++ tailWord_3861188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861188).length < 2 ^ (prefixWord ++ tailWord_3861188).sum := by decide
  have hdescent : baseEnd_3861188 < baseStart_3861188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861201 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3861201 : Nat := 118140960795 + 3861201 * 2 ^ 59
def prefixEnd_3861201 : Nat := 4983230072969 + 3 ^ 40 * 3861201 * 2
def baseEnd_3861201 : Nat := 1321768011080701844686777

theorem tailTrace_3861201 : CollatzResearch.WordTrace tailWord_3861201 prefixEnd_3861201 1321768011080701844686777 := by
  unfold tailWord_3861201
  simp only [CollatzResearch.WordTrace]
  refine ⟨140829570084535692475159457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93886380056357128316772971 140829570084535692475159457)
  ·
    refine ⟨105622177563401769356369593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140829570084535692475159457 105622177563401769356369593)
    ·
      refine ⟨79216633172551327017277195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105622177563401769356369593 79216633172551327017277195)
      ·
        refine ⟨118824949758826990525915793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79216633172551327017277195 118824949758826990525915793)
        ·
          refine ⟨89118712319120242894436845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118824949758826990525915793 89118712319120242894436845)
          ·
            refine ⟨33419517119670091085413817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89118712319120242894436845 33419517119670091085413817)
            ·
              refine ⟨25064637839752568314060363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33419517119670091085413817 25064637839752568314060363)
              ·
                refine ⟨37596956759628852471090545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25064637839752568314060363 37596956759628852471090545)
                ·
                  refine ⟨28197717569721639353317909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37596956759628852471090545 28197717569721639353317909)
                  ·
                    refine ⟨1321768011080701844686777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28197717569721639353317909 1321768011080701844686777)
                    ·
                      rfl

theorem cell22_3861201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3861201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861201 prefixEnd_3861201 := by exact prefixLift 3861201
  have htrace : WordTrace (prefixWord ++ tailWord_3861201) baseStart_3861201 baseEnd_3861201 := by
    simpa [prefixWord, tailWord_3861201, baseEnd_3861201] using wordTrace_append hprefix tailTrace_3861201
  have hstable : (prefixWord ++ tailWord_3861201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861201).length < 2 ^ (prefixWord ++ tailWord_3861201).sum := by decide
  have hdescent : baseEnd_3861201 < baseStart_3861201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861205 : List Nat := [1, 3, 2, 5, 1, 1, 2, 7]
def baseStart_3861205 : Nat := 118140960795 + 3861205 * 2 ^ 59
def prefixEnd_3861205 : Nat := 4983230072969 + 3 ^ 40 * 3861205 * 2
def baseEnd_3861205 : Nat := 146863264484716351954085

theorem tailTrace_3861205 : CollatzResearch.WordTrace tailWord_3861205 prefixEnd_3861205 146863264484716351954085 := by
  unfold tailWord_3861205
  simp only [CollatzResearch.WordTrace]
  refine ⟨140829715976521201158305069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93886477317680800772203379 140829715976521201158305069)
  ·
    refine ⟨52811143491195450434364401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140829715976521201158305069 52811143491195450434364401)
    ·
      refine ⟨39608357618396587825773301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52811143491195450434364401 39608357618396587825773301)
      ·
        refine ⟨3713283526724680108666247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39608357618396587825773301 3713283526724680108666247)
        ·
          refine ⟨5569925290087020162999371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713283526724680108666247 5569925290087020162999371)
          ·
            refine ⟨8354887935130530244499057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569925290087020162999371 8354887935130530244499057)
            ·
              refine ⟨6266165951347897683374293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8354887935130530244499057 6266165951347897683374293)
              ·
                refine ⟨146863264484716351954085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6266165951347897683374293 146863264484716351954085)
                ·
                  rfl

theorem cell22_3861205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 7].length) (baseStart_3861205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861205 prefixEnd_3861205 := by exact prefixLift 3861205
  have htrace : WordTrace (prefixWord ++ tailWord_3861205) baseStart_3861205 baseEnd_3861205 := by
    simpa [prefixWord, tailWord_3861205, baseEnd_3861205] using wordTrace_append hprefix tailTrace_3861205
  have hstable : (prefixWord ++ tailWord_3861205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861205).length < 2 ^ (prefixWord ++ tailWord_3861205).sum := by decide
  have hdescent : baseEnd_3861205 < baseStart_3861205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861250 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3861250 : Nat := 118140960795 + 3861250 * 2 ^ 59
def prefixEnd_3861250 : Nat := 4983230072969 + 3 ^ 40 * 3861250 * 2
def baseEnd_3861250 : Nat := 440594928260694016737209

theorem tailTrace_3861250 : CollatzResearch.WordTrace tailWord_3861250 prefixEnd_3861250 440594928260694016737209 := by
  unfold tailWord_3861250
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207839315339543460923301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93887571507572115895795469 35207839315339543460923301)
  ·
    refine ⟨6601469871626164398923119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35207839315339543460923301 6601469871626164398923119)
    ·
      refine ⟨9902204807439246598384679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601469871626164398923119 9902204807439246598384679)
      ·
        refine ⟨14853307211158869897577019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9902204807439246598384679 14853307211158869897577019)
        ·
          refine ⟨22279960816738304846365529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14853307211158869897577019 22279960816738304846365529)
          ·
            refine ⟨16709970612553728634774147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22279960816738304846365529 16709970612553728634774147)
            ·
              refine ⟨25064955918830592952161221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16709970612553728634774147 25064955918830592952161221)
              ·
                refine ⟨4699679234780736178530229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25064955918830592952161221 4699679234780736178530229)
                ·
                  refine ⟨440594928260694016737209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4699679234780736178530229 440594928260694016737209)
                  ·
                    rfl

theorem cell22_3861250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3861250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861250 prefixEnd_3861250 := by exact prefixLift 3861250
  have htrace : WordTrace (prefixWord ++ tailWord_3861250) baseStart_3861250 baseEnd_3861250 := by
    simpa [prefixWord, tailWord_3861250, baseEnd_3861250] using wordTrace_append hprefix tailTrace_3861250
  have hstable : (prefixWord ++ tailWord_3861250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861250).length < 2 ^ (prefixWord ++ tailWord_3861250).sum := by decide
  have hdescent : baseEnd_3861250 < baseStart_3861250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861308 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_3861308 : Nat := 118140960795 + 3861308 * 2 ^ 59
def prefixEnd_3861308 : Nat := 4983230072969 + 3 ^ 40 * 3861308 * 2
def baseEnd_3861308 : Nat := 1321804639367389232261449

theorem tailTrace_3861308 : CollatzResearch.WordTrace tailWord_3861308 prefixEnd_3861308 1321804639367389232261449 := by
  unfold tailWord_3861308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70416736347574024874652289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93888981796765366499536385 70416736347574024874652289)
  ·
    refine ⟨52812552260680518655989217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70416736347574024874652289 52812552260680518655989217)
    ·
      refine ⟨39609414195510388991991913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52812552260680518655989217 39609414195510388991991913)
      ·
        refine ⟨29707060646632791743993935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39609414195510388991991913 29707060646632791743993935)
        ·
          refine ⟨44560590969949187615990903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29707060646632791743993935 44560590969949187615990903)
          ·
            refine ⟨66840886454923781423986355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44560590969949187615990903 66840886454923781423986355)
            ·
              refine ⟨100261329682385672135979533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66840886454923781423986355 100261329682385672135979533)
              ·
                refine ⟨37597998630894627050992325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100261329682385672135979533 37597998630894627050992325)
                ·
                  refine ⟨7049624743292742572061061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37597998630894627050992325 7049624743292742572061061)
                  ·
                    refine ⟨1321804639367389232261449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7049624743292742572061061 1321804639367389232261449)
                    ·
                      rfl

theorem cell22_3861308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_3861308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861308 prefixEnd_3861308 := by exact prefixLift 3861308
  have htrace : WordTrace (prefixWord ++ tailWord_3861308) baseStart_3861308 baseEnd_3861308 := by
    simpa [prefixWord, tailWord_3861308, baseEnd_3861308] using wordTrace_append hprefix tailTrace_3861308
  have hstable : (prefixWord ++ tailWord_3861308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861308).length < 2 ^ (prefixWord ++ tailWord_3861308).sum := by decide
  have hdescent : baseEnd_3861308 < baseStart_3861308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861340 : List Nat := [2, 2, 4, 2, 1, 2, 1, 8]
def baseStart_3861340 : Nat := 118140960795 + 3861340 * 2 ^ 59
def prefixEnd_3861340 : Nat := 4983230072969 + 3 ^ 40 * 3861340 * 2
def baseEnd_3861340 : Nat := 146868399291261312829039

theorem tailTrace_3861340 : CollatzResearch.WordTrace tailWord_3861340 prefixEnd_3861340 146868399291261312829039 := by
  unfold tailWord_3861340
  simp only [CollatzResearch.WordTrace]
  refine ⟨70417319915516059607234737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93889759887354746142979649 70417319915516059607234737)
  ·
    refine ⟨52812989936637044705426053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70417319915516059607234737 52812989936637044705426053)
    ·
      refine ⟨9902435613119445882267385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52812989936637044705426053 9902435613119445882267385)
      ·
        refine ⟨7426826709839584411700539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9902435613119445882267385 7426826709839584411700539)
        ·
          refine ⟨11140240064759376617550809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426826709839584411700539 11140240064759376617550809)
          ·
            refine ⟨8355180048569532463163107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11140240064759376617550809 8355180048569532463163107)
            ·
              refine ⟨12532770072854298694744661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8355180048569532463163107 12532770072854298694744661)
              ·
                refine ⟨146868399291261312829039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12532770072854298694744661 146868399291261312829039)
                ·
                  rfl

theorem cell22_3861340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_3861340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861340 prefixEnd_3861340 := by exact prefixLift 3861340
  have htrace : WordTrace (prefixWord ++ tailWord_3861340) baseStart_3861340 baseEnd_3861340 := by
    simpa [prefixWord, tailWord_3861340, baseEnd_3861340] using wordTrace_append hprefix tailTrace_3861340
  have hstable : (prefixWord ++ tailWord_3861340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861340).length < 2 ^ (prefixWord ++ tailWord_3861340).sum := by decide
  have hdescent : baseEnd_3861340 < baseStart_3861340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861346 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3861346 : Nat := 118140960795 + 3861346 * 2 ^ 59
def prefixEnd_3861346 : Nat := 4983230072969 + 3 ^ 40 * 3861346 * 2
def baseEnd_3861346 : Nat := 440605882514656599937111

theorem tailTrace_3861346 : CollatzResearch.WordTrace tailWord_3861346 prefixEnd_3861346 440605882514656599937111 := by
  unfold tailWord_3861346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35208714667252595559796973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93889905779340254826125261 35208714667252595559796973)
  ·
    refine ⟨13203268000219723334923865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35208714667252595559796973 13203268000219723334923865)
    ·
      refine ⟨9902451000164792501192899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13203268000219723334923865 9902451000164792501192899)
      ·
        refine ⟨14853676500247188751789349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9902451000164792501192899 14853676500247188751789349)
        ·
          refine ⟨2785064343796347890960503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14853676500247188751789349 2785064343796347890960503)
          ·
            refine ⟨4177596515694521836440755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785064343796347890960503 4177596515694521836440755)
            ·
              refine ⟨6266394773541782754661133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177596515694521836440755 6266394773541782754661133)
              ·
                refine ⟨2349898040078168532997925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6266394773541782754661133 2349898040078168532997925)
                ·
                  refine ⟨440605882514656599937111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2349898040078168532997925 440605882514656599937111)
                  ·
                    rfl

theorem cell22_3861346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3861346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861346 prefixEnd_3861346 := by exact prefixLift 3861346
  have htrace : WordTrace (prefixWord ++ tailWord_3861346) baseStart_3861346 baseEnd_3861346 := by
    simpa [prefixWord, tailWord_3861346, baseEnd_3861346] using wordTrace_append hprefix tailTrace_3861346
  have hstable : (prefixWord ++ tailWord_3861346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861346).length < 2 ^ (prefixWord ++ tailWord_3861346).sum := by decide
  have hdescent : baseEnd_3861346 < baseStart_3861346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861372 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_3861372 : Nat := 118140960795 + 3861372 * 2 ^ 59
def prefixEnd_3861372 : Nat := 4983230072969 + 3 ^ 40 * 3861372 * 2
def baseEnd_3861372 : Nat := 1321826547875314398661253

theorem tailTrace_3861372 : CollatzResearch.WordTrace tailWord_3861372 prefixEnd_3861372 1321826547875314398661253 := by
  unfold tailWord_3861372
  simp only [CollatzResearch.WordTrace]
  refine ⟨70417903483458094339817185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93890537977944125786422913 70417903483458094339817185)
  ·
    refine ⟨52813427612593570754862889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70417903483458094339817185 52813427612593570754862889)
    ·
      refine ⟨39610070709445178066147167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52813427612593570754862889 39610070709445178066147167)
      ·
        refine ⟨59415106064167767099220751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39610070709445178066147167 59415106064167767099220751)
        ·
          refine ⟨89122659096251650648831127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59415106064167767099220751 89122659096251650648831127)
          ·
            refine ⟨133683988644377475973246691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89122659096251650648831127 133683988644377475973246691)
            ·
              refine ⟨200525982966566213959870037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133683988644377475973246691 200525982966566213959870037)
              ·
                refine ⟨2349913862889447819842227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 200525982966566213959870037 2349913862889447819842227)
                ·
                  refine ⟨3524870794334171729763341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349913862889447819842227 3524870794334171729763341)
                  ·
                    refine ⟨1321826547875314398661253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524870794334171729763341 1321826547875314398661253)
                    ·
                      rfl

theorem cell22_3861372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_3861372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861372 prefixEnd_3861372 := by exact prefixLift 3861372
  have htrace : WordTrace (prefixWord ++ tailWord_3861372) baseStart_3861372 baseEnd_3861372 := by
    simpa [prefixWord, tailWord_3861372, baseEnd_3861372] using wordTrace_append hprefix tailTrace_3861372
  have hstable : (prefixWord ++ tailWord_3861372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861372).length < 2 ^ (prefixWord ++ tailWord_3861372).sum := by decide
  have hdescent : baseEnd_3861372 < baseStart_3861372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861385 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 5]
def baseStart_3861385 : Nat := 118140960795 + 3861385 * 2 ^ 59
def prefixEnd_3861385 : Nat := 4983230072969 + 3 ^ 40 * 3861385 * 2
def baseEnd_3861385 : Nat := 440610332680328899362071

theorem tailTrace_3861385 : CollatzResearch.WordTrace tailWord_3861385 prefixEnd_3861385 440610332680328899362071 := by
  unfold tailWord_3861385
  simp only [CollatzResearch.WordTrace]
  refine ⟨140836281115869091899857609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93890854077246061266571739 140836281115869091899857609)
  ·
    refine ⟨105627210836901818924893207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140836281115869091899857609 105627210836901818924893207)
    ·
      refine ⟨158440816255352728387339811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105627210836901818924893207 158440816255352728387339811)
      ·
        refine ⟨237661224383029092581009717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158440816255352728387339811 237661224383029092581009717)
        ·
          refine ⟨22280739785908977429469661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237661224383029092581009717 22280739785908977429469661)
          ·
            refine ⟨8355277419715866536051123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22280739785908977429469661 8355277419715866536051123)
            ·
              refine ⟨12532916129573799804076685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8355277419715866536051123 12532916129573799804076685)
              ·
                refine ⟨4699843548590174926528757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12532916129573799804076685 4699843548590174926528757)
                ·
                  refine ⟨440610332680328899362071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4699843548590174926528757 440610332680328899362071)
                  ·
                    rfl

theorem cell22_3861385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_3861385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861385 prefixEnd_3861385 := by exact prefixLift 3861385
  have htrace : WordTrace (prefixWord ++ tailWord_3861385) baseStart_3861385 baseEnd_3861385 := by
    simpa [prefixWord, tailWord_3861385, baseEnd_3861385] using wordTrace_append hprefix tailTrace_3861385
  have hstable : (prefixWord ++ tailWord_3861385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861385).length < 2 ^ (prefixWord ++ tailWord_3861385).sum := by decide
  have hdescent : baseEnd_3861385 < baseStart_3861385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861443 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_3861443 : Nat := 118140960795 + 3861443 * 2 ^ 59
def prefixEnd_3861443 : Nat := 4983230072969 + 3 ^ 40 * 3861443 * 2
def baseEnd_3861443 : Nat := 1321850852626293880136035

theorem tailTrace_3861443 : CollatzResearch.WordTrace tailWord_3861443 prefixEnd_3861443 1321850852626293880136035 := by
  unfold tailWord_3861443
  simp only [CollatzResearch.WordTrace]
  refine ⟨140838396549658967805468983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93892264366439311870312655 140838396549658967805468983)
  ·
    refine ⟨211257594824488451708203475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140838396549658967805468983 211257594824488451708203475)
    ·
      refine ⟨316886392236732677562305213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211257594824488451708203475 316886392236732677562305213)
      ·
        refine ⟨118832397088774754085864455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316886392236732677562305213 118832397088774754085864455)
        ·
          refine ⟨178248595633162131128796683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118832397088774754085864455 178248595633162131128796683)
          ·
            refine ⟨267372893449743196693195025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178248595633162131128796683 267372893449743196693195025)
            ·
              refine ⟨200529670087307397519896269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267372893449743196693195025 200529670087307397519896269)
              ·
                refine ⟨75198626282740274069961101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200529670087307397519896269 75198626282740274069961101)
                ·
                  refine ⟨28199484856027602776235413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75198626282740274069961101 28199484856027602776235413)
                  ·
                    refine ⟨1321850852626293880136035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28199484856027602776235413 1321850852626293880136035)
                    ·
                      rfl

theorem cell22_3861443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_3861443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861443 prefixEnd_3861443 := by exact prefixLift 3861443
  have htrace : WordTrace (prefixWord ++ tailWord_3861443) baseStart_3861443 baseEnd_3861443 := by
    simpa [prefixWord, tailWord_3861443, baseEnd_3861443] using wordTrace_append hprefix tailTrace_3861443
  have hstable : (prefixWord ++ tailWord_3861443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861443).length < 2 ^ (prefixWord ++ tailWord_3861443).sum := by decide
  have hdescent : baseEnd_3861443 < baseStart_3861443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861479 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3861479 : Nat := 118140960795 + 3861479 * 2 ^ 59
def prefixEnd_3861479 : Nat := 4983230072969 + 3 ^ 40 * 3861479 * 2
def baseEnd_3861479 : Nat := 1321863176162001786235925

theorem tailTrace_3861479 : CollatzResearch.WordTrace tailWord_3861479 prefixEnd_3861479 1321863176162001786235925 := by
  unfold tailWord_3861479
  simp only [CollatzResearch.WordTrace]
  refine ⟨140839709577528545953779491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93893139718352363969186327 140839709577528545953779491)
  ·
    refine ⟨211259564366292818930669237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140839709577528545953779491 211259564366292818930669237)
    ·
      refine ⟨19805584159339951774750241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211259564366292818930669237 19805584159339951774750241)
      ·
        refine ⟨14854188119504963831062681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19805584159339951774750241 14854188119504963831062681)
        ·
          refine ⟨11140641089628722873297011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14854188119504963831062681 11140641089628722873297011)
          ·
            refine ⟨16710961634443084309945517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11140641089628722873297011 16710961634443084309945517)
            ·
              refine ⟨6266610612916156616229569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16710961634443084309945517 6266610612916156616229569)
              ·
                refine ⟨4699957959687117462172177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6266610612916156616229569 4699957959687117462172177)
                ·
                  refine ⟨3524968469765338096629133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4699957959687117462172177 3524968469765338096629133)
                  ·
                    refine ⟨1321863176162001786235925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524968469765338096629133 1321863176162001786235925)
                    ·
                      rfl

theorem cell22_3861479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3861479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861479 prefixEnd_3861479 := by exact prefixLift 3861479
  have htrace : WordTrace (prefixWord ++ tailWord_3861479) baseStart_3861479 baseEnd_3861479 := by
    simpa [prefixWord, tailWord_3861479, baseEnd_3861479] using wordTrace_append hprefix tailTrace_3861479
  have hstable : (prefixWord ++ tailWord_3861479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861479).length < 2 ^ (prefixWord ++ tailWord_3861479).sum := by decide
  have hdescent : baseEnd_3861479 < baseStart_3861479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861541 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_3861541 : Nat := 118140960795 + 3861541 * 2 ^ 59
def prefixEnd_3861541 : Nat := 4983230072969 + 3 ^ 40 * 3861541 * 2
def baseEnd_3861541 : Nat := 1321884400029054291185735

theorem tailTrace_3861541 : CollatzResearch.WordTrace tailWord_3861541 prefixEnd_3861541 1321884400029054291185735 := by
  unfold tailWord_3861541
  simp only [CollatzResearch.WordTrace]
  refine ⟨140841970903303930542536477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93894647268869287028357651 140841970903303930542536477)
  ·
    refine ⟨52815739088738973953451179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140841970903303930542536477 52815739088738973953451179)
    ·
      refine ⟨79223608633108460930176769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52815739088738973953451179 79223608633108460930176769)
      ·
        refine ⟨59417706474831345697632577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79223608633108460930176769 59417706474831345697632577)
        ·
          refine ⟨44563279856123509273224433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59417706474831345697632577 44563279856123509273224433)
          ·
            refine ⟨33422459892092631954918325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44563279856123509273224433 33422459892092631954918325)
            ·
              refine ⟨3133355614883684245773593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33422459892092631954918325 3133355614883684245773593)
              ·
                refine ⟨2350016711162763184330195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133355614883684245773593 2350016711162763184330195)
                ·
                  refine ⟨3525025066744144776495293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350016711162763184330195 3525025066744144776495293)
                  ·
                    refine ⟨1321884400029054291185735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525025066744144776495293 1321884400029054291185735)
                    ·
                      rfl

theorem cell22_3861541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_3861541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861541 prefixEnd_3861541 := by exact prefixLift 3861541
  have htrace : WordTrace (prefixWord ++ tailWord_3861541) baseStart_3861541 baseEnd_3861541 := by
    simpa [prefixWord, tailWord_3861541, baseEnd_3861541] using wordTrace_append hprefix tailTrace_3861541
  have hstable : (prefixWord ++ tailWord_3861541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861541).length < 2 ^ (prefixWord ++ tailWord_3861541).sum := by decide
  have hdescent : baseEnd_3861541 < baseStart_3861541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861614 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3861614 : Nat := 118140960795 + 3861614 * 2 ^ 59
def prefixEnd_3861614 : Nat := 4983230072969 + 3 ^ 40 * 3861614 * 2
def baseEnd_3861614 : Nat := 1321909389420906434110511

theorem tailTrace_3861614 : CollatzResearch.WordTrace tailWord_3861614 prefixEnd_3861614 1321909389420906434110511 := by
  unfold tailWord_3861614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17605579179004933001242987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93896422288026309339962597 17605579179004933001242987)
  ·
    refine ⟨26408368768507399501864481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17605579179004933001242987 26408368768507399501864481)
    ·
      refine ⟨19806276576380549626398361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26408368768507399501864481 19806276576380549626398361)
      ·
        refine ⟨14854707432285412219798771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19806276576380549626398361 14854707432285412219798771)
        ·
          refine ⟨22282061148428118329698157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14854707432285412219798771 22282061148428118329698157)
          ·
            refine ⟨8355772930660544373636809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22282061148428118329698157 8355772930660544373636809)
            ·
              refine ⟨6266829697995408280227607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8355772930660544373636809 6266829697995408280227607)
              ·
                refine ⟨9400244546993112420341411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266829697995408280227607 9400244546993112420341411)
                ·
                  refine ⟨14100366820489668630512117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9400244546993112420341411 14100366820489668630512117)
                  ·
                    refine ⟨1321909389420906434110511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14100366820489668630512117 1321909389420906434110511)
                    ·
                      rfl

theorem cell22_3861614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3861614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861614 prefixEnd_3861614 := by exact prefixLift 3861614
  have htrace : WordTrace (prefixWord ++ tailWord_3861614) baseStart_3861614 baseEnd_3861614 := by
    simpa [prefixWord, tailWord_3861614, baseEnd_3861614] using wordTrace_append hprefix tailTrace_3861614
  have hstable : (prefixWord ++ tailWord_3861614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861614).length < 2 ^ (prefixWord ++ tailWord_3861614).sum := by decide
  have hdescent : baseEnd_3861614 < baseStart_3861614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861710 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_3861710 : Nat := 118140960795 + 3861710 * 2 ^ 59
def prefixEnd_3861710 : Nat := 4983230072969 + 3 ^ 40 * 3861710 * 2
def baseEnd_3861710 : Nat := 1321942252182794183710217

theorem tailTrace_3861710 : CollatzResearch.WordTrace tailWord_3861710 prefixEnd_3861710 1321942252182794183710217 := by
  unfold tailWord_3861710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606016854961459050679823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93898756559794448270292389 17606016854961459050679823)
  ·
    refine ⟨26409025282442188576019735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17606016854961459050679823 26409025282442188576019735)
    ·
      refine ⟨39613537923663282864029603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26409025282442188576019735 39613537923663282864029603)
      ·
        refine ⟨59420306885494924296044405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39613537923663282864029603 59420306885494924296044405)
        ·
          refine ⟨5570653770515149152754163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59420306885494924296044405 5570653770515149152754163)
          ·
            refine ⟨8355980655772723729131245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5570653770515149152754163 8355980655772723729131245)
            ·
              refine ⟨3133492745914771398424217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8355980655772723729131245 3133492745914771398424217)
              ·
                refine ⟨2350119559436078548818163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133492745914771398424217 2350119559436078548818163)
                ·
                  refine ⟨3525179339154117823227245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350119559436078548818163 3525179339154117823227245)
                  ·
                    refine ⟨1321942252182794183710217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525179339154117823227245 1321942252182794183710217)
                    ·
                      rfl

theorem cell22_3861710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_3861710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861710 prefixEnd_3861710 := by exact prefixLift 3861710
  have htrace : WordTrace (prefixWord ++ tailWord_3861710) baseStart_3861710 baseEnd_3861710 := by
    simpa [prefixWord, tailWord_3861710, baseEnd_3861710] using wordTrace_append hprefix tailTrace_3861710
  have hstable : (prefixWord ++ tailWord_3861710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861710).length < 2 ^ (prefixWord ++ tailWord_3861710).sum := by decide
  have hdescent : baseEnd_3861710 < baseStart_3861710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861807 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 7]
def baseStart_3861807 : Nat := 118140960795 + 3861807 * 2 ^ 59
def prefixEnd_3861807 : Nat := 4983230072969 + 3 ^ 40 * 3861807 * 2
def baseEnd_3861807 : Nat := 440658485755039421344973

theorem tailTrace_3861807 : CollatzResearch.WordTrace tailWord_3861807 prefixEnd_3861807 440658485755039421344973 := by
  unfold tailWord_3861807
  simp only [CollatzResearch.WordTrace]
  refine ⟨140851672720340257971719675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93901115146893505314479783 140851672720340257971719675)
  ·
    refine ⟨211277509080510386957579513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140851672720340257971719675 211277509080510386957579513)
    ·
      refine ⟨158458131810382790218184635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211277509080510386957579513 158458131810382790218184635)
      ·
        refine ⟨237687197715574185327276953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158458131810382790218184635 237687197715574185327276953)
        ·
          refine ⟨178265398286680638995457715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237687197715574185327276953 178265398286680638995457715)
          ·
            refine ⟨267398097430020958493186573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178265398286680638995457715 267398097430020958493186573)
            ·
              refine ⟨100274286536257859434944965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267398097430020958493186573 100274286536257859434944965)
              ·
                refine ⟨18801428725548348644052181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100274286536257859434944965 18801428725548348644052181)
                ·
                  refine ⟨440658485755039421344973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18801428725548348644052181 440658485755039421344973)
                  ·
                    rfl

theorem cell22_3861807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_3861807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861807 prefixEnd_3861807 := by exact prefixLift 3861807
  have htrace : WordTrace (prefixWord ++ tailWord_3861807) baseStart_3861807 baseEnd_3861807 := by
    simpa [prefixWord, tailWord_3861807, baseEnd_3861807] using wordTrace_append hprefix tailTrace_3861807
  have hstable : (prefixWord ++ tailWord_3861807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861807).length < 2 ^ (prefixWord ++ tailWord_3861807).sum := by decide
  have hdescent : baseEnd_3861807 < baseStart_3861807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861828 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3861828 : Nat := 118140960795 + 3861828 * 2 ^ 59
def prefixEnd_3861828 : Nat := 4983230072969 + 3 ^ 40 * 3861828 * 2
def baseEnd_3861828 : Nat := 1321982645994281209259855

theorem tailTrace_3861828 : CollatzResearch.WordTrace tailWord_3861828 prefixEnd_3861828 1321982645994281209259855 := by
  unfold tailWord_3861828
  simp only [CollatzResearch.WordTrace]
  refine ⟨70426219326632089279117069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93901625768842785705489425 70426219326632089279117069)
  ·
    refine ⟨26409832247487033479668901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70426219326632089279117069 26409832247487033479668901)
    ·
      refine ⟨4951843546403818777437919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26409832247487033479668901 4951843546403818777437919)
      ·
        refine ⟨7427765319605728166156879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951843546403818777437919 7427765319605728166156879)
        ·
          refine ⟨11141647979408592249235319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427765319605728166156879 11141647979408592249235319)
          ·
            refine ⟨16712471969112888373852979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11141647979408592249235319 16712471969112888373852979)
            ·
              refine ⟨25068707953669332560779469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16712471969112888373852979 25068707953669332560779469)
              ·
                refine ⟨9400765482625999710292301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25068707953669332560779469 9400765482625999710292301)
                ·
                  refine ⟨3525287055984749891359613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9400765482625999710292301 3525287055984749891359613)
                  ·
                    refine ⟨1321982645994281209259855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525287055984749891359613 1321982645994281209259855)
                    ·
                      rfl

theorem cell22_3861828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3861828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861828 prefixEnd_3861828 := by exact prefixLift 3861828
  have htrace : WordTrace (prefixWord ++ tailWord_3861828) baseStart_3861828 baseEnd_3861828 := by
    simpa [prefixWord, tailWord_3861828, baseEnd_3861828] using wordTrace_append hprefix tailTrace_3861828
  have hstable : (prefixWord ++ tailWord_3861828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861828).length < 2 ^ (prefixWord ++ tailWord_3861828).sum := by decide
  have hdescent : baseEnd_3861828 < baseStart_3861828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861841 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 5]
def baseStart_3861841 : Nat := 118140960795 + 3861841 * 2 ^ 59
def prefixEnd_3861841 : Nat := 4983230072969 + 3 ^ 40 * 3861841 * 2
def baseEnd_3861841 : Nat := 440662365386651169561605

theorem tailTrace_3861841 : CollatzResearch.WordTrace tailWord_3861841 prefixEnd_3861841 440662365386651169561605 := by
  unfold tailWord_3861841
  simp only [CollatzResearch.WordTrace]
  refine ⟨140852912802217081778457377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93901941868144721185638251 140852912802217081778457377)
  ·
    refine ⟨105639684601662811333843033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140852912802217081778457377 105639684601662811333843033)
    ·
      refine ⟨79229763451247108500382275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105639684601662811333843033 79229763451247108500382275)
      ·
        refine ⟨118844645176870662750573413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79229763451247108500382275 118844645176870662750573413)
        ·
          refine ⟨22283370970663249265732515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118844645176870662750573413 22283370970663249265732515)
          ·
            refine ⟨33425056455994873898598773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283370970663249265732515 33425056455994873898598773)
            ·
              refine ⟨3133599042749519427993635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33425056455994873898598773 3133599042749519427993635)
              ·
                refine ⟨4700398564124279141990453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133599042749519427993635 4700398564124279141990453)
                ·
                  refine ⟨440662365386651169561605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700398564124279141990453 440662365386651169561605)
                  ·
                    rfl

theorem cell22_3861841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_3861841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861841 prefixEnd_3861841 := by exact prefixLift 3861841
  have htrace : WordTrace (prefixWord ++ tailWord_3861841) baseStart_3861841 baseEnd_3861841 := by
    simpa [prefixWord, tailWord_3861841, baseEnd_3861841] using wordTrace_append hprefix tailTrace_3861841
  have hstable : (prefixWord ++ tailWord_3861841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861841).length < 2 ^ (prefixWord ++ tailWord_3861841).sum := by decide
  have hdescent : baseEnd_3861841 < baseStart_3861841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861899 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 4, 4]
def baseStart_3861899 : Nat := 118140960795 + 3861899 * 2 ^ 59
def prefixEnd_3861899 : Nat := 4983230072969 + 3 ^ 40 * 3861899 * 2
def baseEnd_3861899 : Nat := 1322006950745260690734637

theorem tailTrace_3861899 : CollatzResearch.WordTrace tailWord_3861899 prefixEnd_3861899 1322006950745260690734637 := by
  unfold tailWord_3861899
  simp only [CollatzResearch.WordTrace]
  refine ⟨140855028236006957684068751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93903352157337971789379167 140855028236006957684068751)
  ·
    refine ⟨211282542354010436526103127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140855028236006957684068751 211282542354010436526103127)
    ·
      refine ⟨316923813531015654789154691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211282542354010436526103127 316923813531015654789154691)
      ·
        refine ⟨475385720296523482183732037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316923813531015654789154691 475385720296523482183732037)
        ·
          refine ⟨89134822555598152909449757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475385720296523482183732037 89134822555598152909449757)
          ·
            refine ⟨33425558458349307341043659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89134822555598152909449757 33425558458349307341043659)
            ·
              refine ⟨50138337687523961011565489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33425558458349307341043659 50138337687523961011565489)
              ·
                refine ⟨37603753265642970758674117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50138337687523961011565489 37603753265642970758674117)
                ·
                  refine ⟨7050703737308057017251397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37603753265642970758674117 7050703737308057017251397)
                  ·
                    refine ⟨1322006950745260690734637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7050703737308057017251397 1322006950745260690734637)
                    ·
                      rfl

theorem cell22_3861899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_3861899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861899 prefixEnd_3861899 := by exact prefixLift 3861899
  have htrace : WordTrace (prefixWord ++ tailWord_3861899) baseStart_3861899 baseEnd_3861899 := by
    simpa [prefixWord, tailWord_3861899, baseEnd_3861899] using wordTrace_append hprefix tailTrace_3861899
  have hstable : (prefixWord ++ tailWord_3861899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861899).length < 2 ^ (prefixWord ++ tailWord_3861899).sum := by decide
  have hdescent : baseEnd_3861899 < baseStart_3861899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861914 : List Nat := [3, 1, 1, 4, 1, 1, 1, 10]
def baseStart_3861914 : Nat := 118140960795 + 3861914 * 2 ^ 59
def prefixEnd_3861914 : Nat := 4983230072969 + 3 ^ 40 * 3861914 * 2
def baseEnd_3861914 : Nat := 146890231727978405734399

theorem tailTrace_3861914 : CollatzResearch.WordTrace tailWord_3861914 prefixEnd_3861914 146890231727978405734399 := by
  unfold tailWord_3861914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35213893832738153811466199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93903716887301743497243197 35213893832738153811466199)
  ·
    refine ⟨52820840749107230717199299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35213893832738153811466199 52820840749107230717199299)
    ·
      refine ⟨79231261123660846075798949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52820840749107230717199299 79231261123660846075798949)
      ·
        refine ⟨14855861460686408639212303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79231261123660846075798949 14855861460686408639212303)
        ·
          refine ⟨22283792191029612958818455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14855861460686408639212303 22283792191029612958818455)
          ·
            refine ⟨33425688286544419438227683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283792191029612958818455 33425688286544419438227683)
            ·
              refine ⟨50138532429816629157341525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33425688286544419438227683 50138532429816629157341525)
              ·
                refine ⟨146890231727978405734399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50138532429816629157341525 146890231727978405734399)
                ·
                  rfl

theorem cell22_3861914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_3861914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861914 prefixEnd_3861914 := by exact prefixLift 3861914
  have htrace : WordTrace (prefixWord ++ tailWord_3861914) baseStart_3861914 baseEnd_3861914 := by
    simpa [prefixWord, tailWord_3861914, baseEnd_3861914] using wordTrace_append hprefix tailTrace_3861914
  have hstable : (prefixWord ++ tailWord_3861914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861914).length < 2 ^ (prefixWord ++ tailWord_3861914).sum := by decide
  have hdescent : baseEnd_3861914 < baseStart_3861914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861933 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3861933 : Nat := 118140960795 + 3861933 * 2 ^ 59
def prefixEnd_3861933 : Nat := 4983230072969 + 3 ^ 40 * 3861933 * 2
def baseEnd_3861933 : Nat := 1322018589640095935384533

theorem tailTrace_3861933 : CollatzResearch.WordTrace tailWord_3861933 prefixEnd_3861933 1322018589640095935384533 := by
  unfold tailWord_3861933
  simp only [CollatzResearch.WordTrace]
  refine ⟨140856268317883781490806453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93904178878589187660537635 140856268317883781490806453)
  ·
    refine ⟨13205275154801604514763105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140856268317883781490806453 13205275154801604514763105)
    ·
      refine ⟨9903956366101203386072329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13205275154801604514763105 9903956366101203386072329)
      ·
        refine ⟨7427967274575902539554247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9903956366101203386072329 7427967274575902539554247)
        ·
          refine ⟨11141950911863853809331371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427967274575902539554247 11141950911863853809331371)
          ·
            refine ⟨16712926367795780713997057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11141950911863853809331371 16712926367795780713997057)
            ·
              refine ⟨12534694775846835535497793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16712926367795780713997057 12534694775846835535497793)
              ·
                refine ⟨9401021081885126651623345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12534694775846835535497793 9401021081885126651623345)
                ·
                  refine ⟨7050765811413844988717509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9401021081885126651623345 7050765811413844988717509)
                  ·
                    refine ⟨1322018589640095935384533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7050765811413844988717509 1322018589640095935384533)
                    ·
                      rfl

theorem cell22_3861933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3861933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861933 prefixEnd_3861933 := by exact prefixLift 3861933
  have htrace : WordTrace (prefixWord ++ tailWord_3861933) baseStart_3861933 baseEnd_3861933 := by
    simpa [prefixWord, tailWord_3861933, baseEnd_3861933] using wordTrace_append hprefix tailTrace_3861933
  have hstable : (prefixWord ++ tailWord_3861933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861933).length < 2 ^ (prefixWord ++ tailWord_3861933).sum := by decide
  have hdescent : baseEnd_3861933 < baseStart_3861933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861944 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_3861944 : Nat := 118140960795 + 3861944 * 2 ^ 59
def prefixEnd_3861944 : Nat := 4983230072969 + 3 ^ 40 * 3861944 * 2
def baseEnd_3861944 : Nat := 1322022355164895573359499

theorem tailTrace_3861944 : CollatzResearch.WordTrace tailWord_3861944 prefixEnd_3861944 1322022355164895573359499 := by
  unfold tailWord_3861944
  simp only [CollatzResearch.WordTrace]
  refine ⟨70428334760421965184728443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93904446347229286912971257 70428334760421965184728443)
  ·
    refine ⟨105642502140632947777092665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70428334760421965184728443 105642502140632947777092665)
    ·
      refine ⟨79231876605474710832819499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105642502140632947777092665 79231876605474710832819499)
      ·
        refine ⟨118847814908212066249229249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79231876605474710832819499 118847814908212066249229249)
        ·
          refine ⟨89135861181159049686921937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118847814908212066249229249 89135861181159049686921937)
          ·
            refine ⟨66851895885869287265191453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89135861181159049686921937 66851895885869287265191453)
            ·
              refine ⟨25069460957200982724446795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66851895885869287265191453 25069460957200982724446795)
              ·
                refine ⟨37604191435801474086670193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25069460957200982724446795 37604191435801474086670193)
                ·
                  refine ⟨28203143576851105565002645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37604191435801474086670193 28203143576851105565002645)
                  ·
                    refine ⟨1322022355164895573359499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28203143576851105565002645 1322022355164895573359499)
                    ·
                      rfl

theorem cell22_3861944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_3861944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861944 prefixEnd_3861944 := by exact prefixLift 3861944
  have htrace : WordTrace (prefixWord ++ tailWord_3861944) baseStart_3861944 baseEnd_3861944 := by
    simpa [prefixWord, tailWord_3861944, baseEnd_3861944] using wordTrace_append hprefix tailTrace_3861944
  have hstable : (prefixWord ++ tailWord_3861944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861944).length < 2 ^ (prefixWord ++ tailWord_3861944).sum := by decide
  have hdescent : baseEnd_3861944 < baseStart_3861944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861948 : List Nat := [2, 2, 2, 4, 2, 2, 1, 7]
def baseStart_3861948 : Nat := 118140960795 + 3861948 * 2 ^ 59
def prefixEnd_3861948 : Nat := 4983230072969 + 3 ^ 40 * 3861948 * 2
def baseEnd_3861948 : Nat := 146891524938515655139943

theorem tailTrace_3861948 : CollatzResearch.WordTrace tailWord_3861948 prefixEnd_3861948 146891524938515655139943 := by
  unfold tailWord_3861948
  simp only [CollatzResearch.WordTrace]
  refine ⟨70428407706414719526301249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93904543608552959368401665 70428407706414719526301249)
  ·
    refine ⟨52821305779811039644725937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70428407706414719526301249 52821305779811039644725937)
    ·
      refine ⟨39615979334858279733544453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52821305779811039644725937 39615979334858279733544453)
      ·
        refine ⟨7427996125285927450039585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39615979334858279733544453 7427996125285927450039585)
        ·
          refine ⟨5570997093964445587529689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7427996125285927450039585 5570997093964445587529689)
          ·
            refine ⟨4178247820473334190647267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570997093964445587529689 4178247820473334190647267)
            ·
              refine ⟨6267371730710001285970901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178247820473334190647267 6267371730710001285970901)
              ·
                refine ⟨146891524938515655139943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6267371730710001285970901 146891524938515655139943)
                ·
                  rfl

theorem cell22_3861948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 7].length) (baseStart_3861948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861948 prefixEnd_3861948 := by exact prefixLift 3861948
  have htrace : WordTrace (prefixWord ++ tailWord_3861948) baseStart_3861948 baseEnd_3861948 := by
    simpa [prefixWord, tailWord_3861948, baseEnd_3861948] using wordTrace_append hprefix tailTrace_3861948
  have hstable : (prefixWord ++ tailWord_3861948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861948).length < 2 ^ (prefixWord ++ tailWord_3861948).sum := by decide
  have hdescent : baseEnd_3861948 < baseStart_3861948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861991 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3861991 : Nat := 118140960795 + 3861991 * 2 ^ 59
def prefixEnd_3861991 : Nat := 4983230072969 + 3 ^ 40 * 3861991 * 2
def baseEnd_3861991 : Nat := 1322038444225403117434355

theorem tailTrace_3861991 : CollatzResearch.WordTrace tailWord_3861991 prefixEnd_3861991 1322038444225403117434355 := by
  unfold tailWord_3861991
  simp only [CollatzResearch.WordTrace]
  refine ⟨140858383751673657396417827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93905589167782438264278551 140858383751673657396417827)
  ·
    refine ⟨211287575627510486094626741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140858383751673657396417827 211287575627510486094626741)
    ·
      refine ⟨19808210215079108071371257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211287575627510486094626741 19808210215079108071371257)
      ·
        refine ⟨14856157661309331053528443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19808210215079108071371257 14856157661309331053528443)
        ·
          refine ⟨22284236491963996580292665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14856157661309331053528443 22284236491963996580292665)
          ·
            refine ⟨16713177368972997435219499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22284236491963996580292665 16713177368972997435219499)
            ·
              refine ⟨25069766053459496152829249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16713177368972997435219499 25069766053459496152829249)
              ·
                refine ⟨18802324540094622114621937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25069766053459496152829249 18802324540094622114621937)
                ·
                  refine ⟨14101743405070966585966453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18802324540094622114621937 14101743405070966585966453)
                  ·
                    refine ⟨1322038444225403117434355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14101743405070966585966453 1322038444225403117434355)
                    ·
                      rfl

theorem cell22_3861991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3861991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3861991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3861991 prefixEnd_3861991 := by exact prefixLift 3861991
  have htrace : WordTrace (prefixWord ++ tailWord_3861991) baseStart_3861991 baseEnd_3861991 := by
    simpa [prefixWord, tailWord_3861991, baseEnd_3861991] using wordTrace_append hprefix tailTrace_3861991
  have hstable : (prefixWord ++ tailWord_3861991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861991).length < 2 ^ (prefixWord ++ tailWord_3861991).sum := by decide
  have hdescent : baseEnd_3861991 < baseStart_3861991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862023 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 1, 4]
def baseStart_3862023 : Nat := 118140960795 + 3862023 * 2 ^ 59
def prefixEnd_3862023 : Nat := 4983230072969 + 3 ^ 40 * 3862023 * 2
def baseEnd_3862023 : Nat := 1322049398479365700634257

theorem tailTrace_3862023 : CollatzResearch.WordTrace tailWord_3862023 prefixEnd_3862023 1322049398479365700634257 := by
  unfold tailWord_3862023
  simp only [CollatzResearch.WordTrace]
  refine ⟨140859550887557726861582723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93906367258371817907721815 140859550887557726861582723)
  ·
    refine ⟨211289326331336590292374085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140859550887557726861582723 211289326331336590292374085)
    ·
      refine ⟨39616748687125610679820141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211289326331336590292374085 39616748687125610679820141)
      ·
        refine ⟨14856280757672104004932553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39616748687125610679820141 14856280757672104004932553)
        ·
          refine ⟨11142210568254078003699415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14856280757672104004932553 11142210568254078003699415)
          ·
            refine ⟨16713315852381117005549123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142210568254078003699415 16713315852381117005549123)
            ·
              refine ⟨25069973778571675508323685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16713315852381117005549123 25069973778571675508323685)
              ·
                refine ⟨4700620083482189157810691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25069973778571675508323685 4700620083482189157810691)
                ·
                  refine ⟨7050930125223283736716037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700620083482189157810691 7050930125223283736716037)
                  ·
                    refine ⟨1322049398479365700634257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7050930125223283736716037 1322049398479365700634257)
                    ·
                      rfl

theorem cell22_3862023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_3862023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862023 prefixEnd_3862023 := by exact prefixLift 3862023
  have htrace : WordTrace (prefixWord ++ tailWord_3862023) baseStart_3862023 baseEnd_3862023 := by
    simpa [prefixWord, tailWord_3862023, baseEnd_3862023] using wordTrace_append hprefix tailTrace_3862023
  have hstable : (prefixWord ++ tailWord_3862023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862023).length < 2 ^ (prefixWord ++ tailWord_3862023).sum := by decide
  have hdescent : baseEnd_3862023 < baseStart_3862023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862053 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_3862053 : Nat := 118140960795 + 3862053 * 2 ^ 59
def prefixEnd_3862053 : Nat := 4983230072969 + 3 ^ 40 * 3862053 * 2
def baseEnd_3862053 : Nat := 1322059668092455622384165

theorem tailTrace_3862053 : CollatzResearch.WordTrace tailWord_3862053 prefixEnd_3862053 1322059668092455622384165 := by
  unfold tailWord_3862053
  simp only [CollatzResearch.WordTrace]
  refine ⟨140860645077449041985174813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93907096718299361323449875 140860645077449041985174813)
  ·
    refine ⟨52822741904043390744440555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140860645077449041985174813 52822741904043390744440555)
    ·
      refine ⟨79234112856065086116660833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52822741904043390744440555 79234112856065086116660833)
      ·
        refine ⟨59425584642048814587495625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79234112856065086116660833 59425584642048814587495625)
        ·
          refine ⟨44569188481536610940621719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59425584642048814587495625 44569188481536610940621719)
          ·
            refine ⟨66853782722304916410932579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44569188481536610940621719 66853782722304916410932579)
            ·
              refine ⟨100280674083457374616398869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66853782722304916410932579 100280674083457374616398869)
              ·
                refine ⟨4700656597662064435143697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100280674083457374616398869 4700656597662064435143697)
                ·
                  refine ⟨3525492448246548326357773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4700656597662064435143697 3525492448246548326357773)
                  ·
                    refine ⟨1322059668092455622384165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525492448246548326357773 1322059668092455622384165)
                    ·
                      rfl

theorem cell22_3862053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_3862053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862053 prefixEnd_3862053 := by exact prefixLift 3862053
  have htrace : WordTrace (prefixWord ++ tailWord_3862053) baseStart_3862053 baseEnd_3862053 := by
    simpa [prefixWord, tailWord_3862053, baseEnd_3862053] using wordTrace_append hprefix tailTrace_3862053
  have hstable : (prefixWord ++ tailWord_3862053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862053).length < 2 ^ (prefixWord ++ tailWord_3862053).sum := by decide
  have hdescent : baseEnd_3862053 < baseStart_3862053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862128 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_3862128 : Nat := 118140960795 + 3862128 * 2 ^ 59
def prefixEnd_3862128 : Nat := 4983230072969 + 3 ^ 40 * 3862128 * 2
def baseEnd_3862128 : Nat := 440695114041726808919645

theorem tailTrace_3862128 : CollatzResearch.WordTrace tailWord_3862128 prefixEnd_3862128 440695114041726808919645 := by
  unfold tailWord_3862128
  simp only [CollatzResearch.WordTrace]
  refine ⟨70431690276088664897077519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93908920368118219862770025 70431690276088664897077519)
  ·
    refine ⟨105647535414132997345616279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70431690276088664897077519 105647535414132997345616279)
    ·
      refine ⟨158471303121199496018424419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105647535414132997345616279 158471303121199496018424419)
      ·
        refine ⟨237706954681799244027636629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158471303121199496018424419 237706954681799244027636629)
        ·
          refine ⟨11142513500709339563795467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237706954681799244027636629 11142513500709339563795467)
          ·
            refine ⟨16713770251064009345693201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142513500709339563795467 16713770251064009345693201)
            ·
              refine ⟨12535327688298007009269901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16713770251064009345693201 12535327688298007009269901)
              ·
                refine ⟨4700747883111752628476213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12535327688298007009269901 4700747883111752628476213)
                ·
                  refine ⟨440695114041726808919645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700747883111752628476213 440695114041726808919645)
                  ·
                    rfl

theorem cell22_3862128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_3862128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862128 prefixEnd_3862128 := by exact prefixLift 3862128
  have htrace : WordTrace (prefixWord ++ tailWord_3862128) baseStart_3862128 baseEnd_3862128 := by
    simpa [prefixWord, tailWord_3862128, baseEnd_3862128] using wordTrace_append hprefix tailTrace_3862128
  have hstable : (prefixWord ++ tailWord_3862128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862128).length < 2 ^ (prefixWord ++ tailWord_3862128).sum := by decide
  have hdescent : baseEnd_3862128 < baseStart_3862128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862156 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_3862156 : Nat := 118140960795 + 3862156 * 2 ^ 59
def prefixEnd_3862156 : Nat := 4983230072969 + 3 ^ 40 * 3862156 * 2
def baseEnd_3862156 : Nat := 440698309032465895686283

theorem tailTrace_3862156 : CollatzResearch.WordTrace tailWord_3862156 prefixEnd_3862156 440698309032465895686283 := by
  unfold tailWord_3862156
  simp only [CollatzResearch.WordTrace]
  refine ⟨70432200898037945288087161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93909601197383927050782881 70432200898037945288087161)
  ·
    refine ⟨52824150673528458966065371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70432200898037945288087161 52824150673528458966065371)
    ·
      refine ⟨79236226010292688449098057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52824150673528458966065371 79236226010292688449098057)
      ·
        refine ⟨59427169507719516336823543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79236226010292688449098057 59427169507719516336823543)
        ·
          refine ⟨89140754261579274505235315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59427169507719516336823543 89140754261579274505235315)
          ·
            refine ⟨133711131392368911757852973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89140754261579274505235315 133711131392368911757852973)
            ·
              refine ⟨50141674272138341909194865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133711131392368911757852973 50141674272138341909194865)
              ·
                refine ⟨37606255704103756431896149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50141674272138341909194865 37606255704103756431896149)
                ·
                  refine ⟨440698309032465895686283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37606255704103756431896149 440698309032465895686283)
                  ·
                    rfl

theorem cell22_3862156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_3862156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862156 prefixEnd_3862156 := by exact prefixLift 3862156
  have htrace : WordTrace (prefixWord ++ tailWord_3862156) baseStart_3862156 baseEnd_3862156 := by
    simpa [prefixWord, tailWord_3862156, baseEnd_3862156] using wordTrace_append hprefix tailTrace_3862156
  have hstable : (prefixWord ++ tailWord_3862156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862156).length < 2 ^ (prefixWord ++ tailWord_3862156).sum := by decide
  have hdescent : baseEnd_3862156 < baseStart_3862156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862162 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3862162 : Nat := 118140960795 + 3862162 * 2 ^ 59
def prefixEnd_3862162 : Nat := 4983230072969 + 3 ^ 40 * 3862162 * 2
def baseEnd_3862162 : Nat := 440698993673338557136277

theorem tailTrace_3862162 : CollatzResearch.WordTrace tailWord_3862162 prefixEnd_3862162 440698993673338557136277 := by
  unfold tailWord_3862162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216155158513538400223185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93909747089369435733928493 35216155158513538400223185)
  ·
    refine ⟨26412116368885153800167389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35216155158513538400223185 26412116368885153800167389)
    ·
      refine ⟨9904543638331932675062771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26412116368885153800167389 9904543638331932675062771)
      ·
        refine ⟨14856815457497899012594157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904543638331932675062771 14856815457497899012594157)
        ·
          refine ⟨5571305796561712129722809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14856815457497899012594157 5571305796561712129722809)
          ·
            refine ⟨4178479347421284097292107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571305796561712129722809 4178479347421284097292107)
            ·
              refine ⟨6267719021131926145938161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178479347421284097292107 6267719021131926145938161)
              ·
                refine ⟨4700789265848944609453621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267719021131926145938161 4700789265848944609453621)
                ·
                  refine ⟨440698993673338557136277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700789265848944609453621 440698993673338557136277)
                  ·
                    rfl

theorem cell22_3862162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3862162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862162 prefixEnd_3862162 := by exact prefixLift 3862162
  have htrace : WordTrace (prefixWord ++ tailWord_3862162) baseStart_3862162 baseEnd_3862162 := by
    simpa [prefixWord, tailWord_3862162, baseEnd_3862162] using wordTrace_append hprefix tailTrace_3862162
  have hstable : (prefixWord ++ tailWord_3862162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862162).length < 2 ^ (prefixWord ++ tailWord_3862162).sum := by decide
  have hdescent : baseEnd_3862162 < baseStart_3862162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862250 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3862250 : Nat := 118140960795 + 3862250 * 2 ^ 59
def prefixEnd_3862250 : Nat := 4983230072969 + 3 ^ 40 * 3862250 * 2
def baseEnd_3862250 : Nat := 1322127105218412775208561

theorem tailTrace_3862250 : CollatzResearch.WordTrace tailWord_3862250 prefixEnd_3862250 1322127105218412775208561 := by
  unfold tailWord_3862250
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216957564433836157524051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93911886838490229753397469 35216957564433836157524051)
  ·
    refine ⟨52825436346650754236286077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35216957564433836157524051 52825436346650754236286077)
    ·
      refine ⟨19809538629994032838607279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52825436346650754236286077 19809538629994032838607279)
      ·
        refine ⟨29714307944991049257910919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19809538629994032838607279 29714307944991049257910919)
        ·
          refine ⟨44571461917486573886866379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29714307944991049257910919 44571461917486573886866379)
          ·
            refine ⟨66857192876229860830299569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44571461917486573886866379 66857192876229860830299569)
            ·
              refine ⟨50142894657172395622724677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66857192876229860830299569 50142894657172395622724677)
              ·
                refine ⟨9401792748219824179260877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50142894657172395622724677 9401792748219824179260877)
                ·
                  refine ⟨3525672280582434067222829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9401792748219824179260877 3525672280582434067222829)
                  ·
                    refine ⟨1322127105218412775208561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525672280582434067222829 1322127105218412775208561)
                    ·
                      rfl

theorem cell22_3862250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3862250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862250 prefixEnd_3862250 := by exact prefixLift 3862250
  have htrace : WordTrace (prefixWord ++ tailWord_3862250) baseStart_3862250 baseEnd_3862250 := by
    simpa [prefixWord, tailWord_3862250, baseEnd_3862250] using wordTrace_append hprefix tailTrace_3862250
  have hstable : (prefixWord ++ tailWord_3862250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862250).length < 2 ^ (prefixWord ++ tailWord_3862250).sum := by decide
  have hdescent : baseEnd_3862250 < baseStart_3862250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862280 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_3862280 : Nat := 118140960795 + 3862280 * 2 ^ 59
def prefixEnd_3862280 : Nat := 4983230072969 + 3 ^ 40 * 3862280 * 2
def baseEnd_3862280 : Nat := 440712458277167565652823

theorem tailTrace_3862280 : CollatzResearch.WordTrace tailWord_3862280 prefixEnd_3862280 440712458277167565652823 := by
  unfold tailWord_3862280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70434462223813329876844147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93912616298417773169125529 70434462223813329876844147)
  ·
    refine ⟨105651693335719994815266221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70434462223813329876844147 105651693335719994815266221)
    ·
      refine ⟨39619385000894998055724833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105651693335719994815266221 39619385000894998055724833)
      ·
        refine ⟨29714538750671248541793625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39619385000894998055724833 29714538750671248541793625)
        ·
          refine ⟨22285904063003436406345219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29714538750671248541793625 22285904063003436406345219)
          ·
            refine ⟨33428856094505154609517829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22285904063003436406345219 33428856094505154609517829)
            ·
              refine ⟨6267910517719716489284593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33428856094505154609517829 6267910517719716489284593)
              ·
                refine ⟨4700932888289787366963445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267910517719716489284593 4700932888289787366963445)
                ·
                  refine ⟨440712458277167565652823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700932888289787366963445 440712458277167565652823)
                  ·
                    rfl

theorem cell22_3862280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_3862280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862280 prefixEnd_3862280 := by exact prefixLift 3862280
  have htrace : WordTrace (prefixWord ++ tailWord_3862280) baseStart_3862280 baseEnd_3862280 := by
    simpa [prefixWord, tailWord_3862280, baseEnd_3862280] using wordTrace_append hprefix tailTrace_3862280
  have hstable : (prefixWord ++ tailWord_3862280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862280).length < 2 ^ (prefixWord ++ tailWord_3862280).sum := by decide
  have hdescent : baseEnd_3862280 < baseStart_3862280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862284 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_3862284 : Nat := 118140960795 + 3862284 * 2 ^ 59
def prefixEnd_3862284 : Nat := 4983230072969 + 3 ^ 40 * 3862284 * 2
def baseEnd_3862284 : Nat := 1322138744113248019858457

theorem tailTrace_3862284 : CollatzResearch.WordTrace tailWord_3862284 prefixEnd_3862284 1322138744113248019858457 := by
  unfold tailWord_3862284
  simp only [CollatzResearch.WordTrace]
  refine ⟨70434535169806084218416953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93912713559741445624555937 70434535169806084218416953)
  ·
    refine ⟨52825901377354563163812715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70434535169806084218416953 52825901377354563163812715)
    ·
      refine ⟨79238852066031844745719073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52825901377354563163812715 79238852066031844745719073)
      ·
        refine ⟨59429139049523883559289305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79238852066031844745719073 59429139049523883559289305)
        ·
          refine ⟨44571854287142912669466979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59429139049523883559289305 44571854287142912669466979)
          ·
            refine ⟨66857781430714369004200469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44571854287142912669466979 66857781430714369004200469)
            ·
              refine ⟨3133958504564736047071897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66857781430714369004200469 3133958504564736047071897)
              ·
                refine ⟨2350468878423552035303923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133958504564736047071897 2350468878423552035303923)
                ·
                  refine ⟨3525703317635328052955885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350468878423552035303923 3525703317635328052955885)
                  ·
                    refine ⟨1322138744113248019858457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525703317635328052955885 1322138744113248019858457)
                    ·
                      rfl

theorem cell22_3862284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_3862284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862284 prefixEnd_3862284 := by exact prefixLift 3862284
  have htrace : WordTrace (prefixWord ++ tailWord_3862284) baseStart_3862284 baseEnd_3862284 := by
    simpa [prefixWord, tailWord_3862284, baseEnd_3862284] using wordTrace_append hprefix tailTrace_3862284
  have hstable : (prefixWord ++ tailWord_3862284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862284).length < 2 ^ (prefixWord ++ tailWord_3862284).sum := by decide
  have hdescent : baseEnd_3862284 < baseStart_3862284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862295 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 2, 5]
def baseStart_3862295 : Nat := 118140960795 + 3862295 * 2 ^ 59
def prefixEnd_3862295 : Nat := 4983230072969 + 3 ^ 40 * 3862295 * 2
def baseEnd_3862295 : Nat := 1322142509638047657833423

theorem tailTrace_3862295 : CollatzResearch.WordTrace tailWord_3862295 prefixEnd_3862295 1322142509638047657833423 := by
  unfold tailWord_3862295
  simp only [CollatzResearch.WordTrace]
  refine ⟨140869471542572317315484339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93912981028381544876989559 140869471542572317315484339)
  ·
    refine ⟨211304207313858475973226509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140869471542572317315484339 211304207313858475973226509)
    ·
      refine ⟨79239077742696928489959941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211304207313858475973226509 79239077742696928489959941)
      ·
        refine ⟨14857327076755674091867489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79239077742696928489959941 14857327076755674091867489)
        ·
          refine ⟨11142995307566755568900617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14857327076755674091867489 11142995307566755568900617)
          ·
            refine ⟨8357246480675066676675463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11142995307566755568900617 8357246480675066676675463)
            ·
              refine ⟨12535869721012600015013195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8357246480675066676675463 12535869721012600015013195)
              ·
                refine ⟨18803804581518900022519793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12535869721012600015013195 18803804581518900022519793)
                ·
                  refine ⟨14102853436139175016889845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18803804581518900022519793 14102853436139175016889845)
                  ·
                    refine ⟨1322142509638047657833423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14102853436139175016889845 1322142509638047657833423)
                    ·
                      rfl

theorem cell22_3862295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_3862295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862295 prefixEnd_3862295 := by exact prefixLift 3862295
  have htrace : WordTrace (prefixWord ++ tailWord_3862295) baseStart_3862295 baseEnd_3862295 := by
    simpa [prefixWord, tailWord_3862295, baseEnd_3862295] using wordTrace_append hprefix tailTrace_3862295
  have hstable : (prefixWord ++ tailWord_3862295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862295).length < 2 ^ (prefixWord ++ tailWord_3862295).sum := by decide
  have hdescent : baseEnd_3862295 < baseStart_3862295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862357 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3862357 : Nat := 118140960795 + 3862357 * 2 ^ 59
def prefixEnd_3862357 : Nat := 4983230072969 + 3 ^ 40 * 3862357 * 2
def baseEnd_3862357 : Nat := 1322163733505100162783233

theorem tailTrace_3862357 : CollatzResearch.WordTrace tailWord_3862357 prefixEnd_3862357 1322163733505100162783233 := by
  unfold tailWord_3862357
  simp only [CollatzResearch.WordTrace]
  refine ⟨140871732868347701904241325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93914488578898467936160883 140871732868347701904241325)
  ·
    refine ⟨52826899825630388214090497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140871732868347701904241325 52826899825630388214090497)
    ·
      refine ⟨39620174869222791160567873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52826899825630388214090497 39620174869222791160567873)
      ·
        refine ⟨29715131151917093370425905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39620174869222791160567873 29715131151917093370425905)
        ·
          refine ⟨22286348363937820027819429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29715131151917093370425905 22286348363937820027819429)
          ·
            refine ⟨4178690318238341255216143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22286348363937820027819429 4178690318238341255216143)
            ·
              refine ⟨6268035477357511882824215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178690318238341255216143 6268035477357511882824215)
              ·
                refine ⟨9402053216036267824236323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268035477357511882824215 9402053216036267824236323)
                ·
                  refine ⟨14103079824054401736354485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402053216036267824236323 14103079824054401736354485)
                  ·
                    refine ⟨1322163733505100162783233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14103079824054401736354485 1322163733505100162783233)
                    ·
                      rfl

theorem cell22_3862357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3862357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862357 prefixEnd_3862357 := by exact prefixLift 3862357
  have htrace : WordTrace (prefixWord ++ tailWord_3862357) baseStart_3862357 baseEnd_3862357 := by
    simpa [prefixWord, tailWord_3862357, baseEnd_3862357] using wordTrace_append hprefix tailTrace_3862357
  have hstable : (prefixWord ++ tailWord_3862357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862357).length < 2 ^ (prefixWord ++ tailWord_3862357).sum := by decide
  have hdescent : baseEnd_3862357 < baseStart_3862357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862383 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_3862383 : Nat := 118140960795 + 3862383 * 2 ^ 59
def prefixEnd_3862383 : Nat := 4983230072969 + 3 ^ 40 * 3862383 * 2
def baseEnd_3862383 : Nat := 1322172633836444761633153

theorem tailTrace_3862383 : CollatzResearch.WordTrace tailWord_3862383 prefixEnd_3862383 1322172633836444761633153 := by
  unfold tailWord_3862383
  simp only [CollatzResearch.WordTrace]
  refine ⟨140872681166253508344687803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93915120777502338896458535 140872681166253508344687803)
  ·
    refine ⟨211309021749380262517031705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140872681166253508344687803 211309021749380262517031705)
    ·
      refine ⟨158481766312035196887773779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211309021749380262517031705 158481766312035196887773779)
      ·
        refine ⟨237722649468052795331660669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158481766312035196887773779 237722649468052795331660669)
        ·
          refine ⟨89145993550519798249372751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237722649468052795331660669 89145993550519798249372751)
          ·
            refine ⟨133718990325779697374059127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89145993550519798249372751 133718990325779697374059127)
            ·
              refine ⟨200578485488669546061088691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133718990325779697374059127 200578485488669546061088691)
              ·
                refine ⟨300867728233004319091633037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200578485488669546061088691 300867728233004319091633037)
                ·
                  refine ⟨112825398087376619659362389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300867728233004319091633037 112825398087376619659362389)
                  ·
                    refine ⟨1322172633836444761633153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112825398087376619659362389 1322172633836444761633153)
                    ·
                      rfl

theorem cell22_3862383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_3862383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862383 prefixEnd_3862383 := by exact prefixLift 3862383
  have htrace : WordTrace (prefixWord ++ tailWord_3862383) baseStart_3862383 baseEnd_3862383 := by
    simpa [prefixWord, tailWord_3862383, baseEnd_3862383] using wordTrace_append hprefix tailTrace_3862383
  have hstable : (prefixWord ++ tailWord_3862383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862383).length < 2 ^ (prefixWord ++ tailWord_3862383).sum := by decide
  have hdescent : baseEnd_3862383 < baseStart_3862383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862408 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 2, 3]
def baseStart_3862408 : Nat := 118140960795 + 3862408 * 2 ^ 59
def prefixEnd_3862408 : Nat := 4983230072969 + 3 ^ 40 * 3862408 * 2
def baseEnd_3862408 : Nat := 1322181191847353029758077

theorem tailTrace_3862408 : CollatzResearch.WordTrace tailWord_3862408 prefixEnd_3862408 1322181191847353029758077 := by
  unfold tailWord_3862408
  simp only [CollatzResearch.WordTrace]
  refine ⟨70436796495581468807173939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93915728660775291742898585 70436796495581468807173939)
  ·
    refine ⟨105655194743372203210760909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70436796495581468807173939 105655194743372203210760909)
    ·
      refine ⟨39620698028764576204035341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105655194743372203210760909 39620698028764576204035341)
      ·
        refine ⟨14857761760786716076513253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39620698028764576204035341 14857761760786716076513253)
        ·
          refine ⟨2785830330147509264346235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14857761760786716076513253 2785830330147509264346235)
          ·
            refine ⟨4178745495221263896519353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785830330147509264346235 4178745495221263896519353)
            ·
              refine ⟨3134059121415947922389515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178745495221263896519353 3134059121415947922389515)
              ·
                refine ⟨4701088682123921883584273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134059121415947922389515 4701088682123921883584273)
                ·
                  refine ⟨3525816511592941412688205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4701088682123921883584273 3525816511592941412688205)
                  ·
                    refine ⟨1322181191847353029758077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525816511592941412688205 1322181191847353029758077)
                    ·
                      rfl

theorem cell22_3862408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_3862408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862408 prefixEnd_3862408 := by exact prefixLift 3862408
  have htrace : WordTrace (prefixWord ++ tailWord_3862408) baseStart_3862408 baseEnd_3862408 := by
    simpa [prefixWord, tailWord_3862408, baseEnd_3862408] using wordTrace_append hprefix tailTrace_3862408
  have hstable : (prefixWord ++ tailWord_3862408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862408).length < 2 ^ (prefixWord ++ tailWord_3862408).sum := by decide
  have hdescent : baseEnd_3862408 < baseStart_3862408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862453 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3862453 : Nat := 118140960795 + 3862453 * 2 ^ 59
def prefixEnd_3862453 : Nat := 4983230072969 + 3 ^ 40 * 3862453 * 2
def baseEnd_3862453 : Nat := 1322196596266987912382939

theorem tailTrace_3862453 : CollatzResearch.WordTrace tailWord_3862453 prefixEnd_3862453 1322196596266987912382939 := by
  unfold tailWord_3862453
  simp only [CollatzResearch.WordTrace]
  refine ⟨140875234275999910299736013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93916822850666606866490675 140875234275999910299736013)
  ·
    refine ⟨52828212853499966362401005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140875234275999910299736013 52828212853499966362401005)
    ·
      refine ⟨19810579820062487385900377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52828212853499966362401005 19810579820062487385900377)
      ·
        refine ⟨14857934865046865539425283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19810579820062487385900377 14857934865046865539425283)
        ·
          refine ⟨22286902297570298309137925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14857934865046865539425283 22286902297570298309137925)
          ·
            refine ⟨4178794180794430932963361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22286902297570298309137925 4178794180794430932963361)
            ·
              refine ⟨3134095635595823199722521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178794180794430932963361 3134095635595823199722521)
              ·
                refine ⟨2350571726696867399791891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3134095635595823199722521 2350571726696867399791891)
                ·
                  refine ⟨3525857590045301099687837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350571726696867399791891 3525857590045301099687837)
                  ·
                    refine ⟨1322196596266987912382939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525857590045301099687837 1322196596266987912382939)
                    ·
                      rfl

theorem cell22_3862453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3862453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862453 prefixEnd_3862453 := by exact prefixLift 3862453
  have htrace : WordTrace (prefixWord ++ tailWord_3862453) baseStart_3862453 baseEnd_3862453 := by
    simpa [prefixWord, tailWord_3862453, baseEnd_3862453] using wordTrace_append hprefix tailTrace_3862453
  have hstable : (prefixWord ++ tailWord_3862453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862453).length < 2 ^ (prefixWord ++ tailWord_3862453).sum := by decide
  have hdescent : baseEnd_3862453 < baseStart_3862453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862462 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3862462 : Nat := 118140960795 + 3862462 * 2 ^ 59
def prefixEnd_3862462 : Nat := 4983230072969 + 3 ^ 40 * 3862462 * 2
def baseEnd_3862462 : Nat := 1322199677150914888907911

theorem tailTrace_3862462 : CollatzResearch.WordTrace tailWord_3862462 prefixEnd_3862462 1322199677150914888907911 := by
  unfold tailWord_3862462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17609445316620913104601705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93917041688644869891209093 17609445316620913104601705)
  ·
    refine ⟨13207083987465684828451279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17609445316620913104601705 13207083987465684828451279)
    ·
      refine ⟨19810625981198527242676919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13207083987465684828451279 19810625981198527242676919)
      ·
        refine ⟨29715938971797790864015379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19810625981198527242676919 29715938971797790864015379)
        ·
          refine ⟨44573908457696686296023069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29715938971797790864015379 44573908457696686296023069)
          ·
            refine ⟨16715215671636257361008651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44573908457696686296023069 16715215671636257361008651)
            ·
              refine ⟨25072823507454386041512977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16715215671636257361008651 25072823507454386041512977)
              ·
                refine ⟨18804617630590789531134733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25072823507454386041512977 18804617630590789531134733)
                ·
                  refine ⟨7051731611471546074175525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18804617630590789531134733 7051731611471546074175525)
                  ·
                    refine ⟨1322199677150914888907911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7051731611471546074175525 1322199677150914888907911)
                    ·
                      rfl

theorem cell22_3862462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3862462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862462 prefixEnd_3862462 := by exact prefixLift 3862462
  have htrace : WordTrace (prefixWord ++ tailWord_3862462) baseStart_3862462 baseEnd_3862462 := by
    simpa [prefixWord, tailWord_3862462, baseEnd_3862462] using wordTrace_append hprefix tailTrace_3862462
  have hstable : (prefixWord ++ tailWord_3862462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862462).length < 2 ^ (prefixWord ++ tailWord_3862462).sum := by decide
  have hdescent : baseEnd_3862462 < baseStart_3862462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862526 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3862526 : Nat := 118140960795 + 3862526 * 2 ^ 59
def prefixEnd_3862526 : Nat := 4983230072969 + 3 ^ 40 * 3862526 * 2
def baseEnd_3862526 : Nat := 1322221585658840055307715

theorem tailTrace_3862526 : CollatzResearch.WordTrace tailWord_3862526 prefixEnd_3862526 1322221585658840055307715 := by
  unfold tailWord_3862526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17609737100591930470892929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93918597869823629178095621 17609737100591930470892929)
  ·
    refine ⟨13207302825443947853169697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17609737100591930470892929 13207302825443947853169697)
    ·
      refine ⟨9905477119082960889877273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13207302825443947853169697 9905477119082960889877273)
      ·
        refine ⟨7429107839312220667407955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9905477119082960889877273 7429107839312220667407955)
        ·
          refine ⟨11143661758968331001111933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7429107839312220667407955 11143661758968331001111933)
          ·
            refine ⟨4178873159613124125416975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11143661758968331001111933 4178873159613124125416975)
            ·
              refine ⟨6268309739419686188125463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178873159613124125416975 6268309739419686188125463)
              ·
                refine ⟨9402464609129529282188195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268309739419686188125463 9402464609129529282188195)
                ·
                  refine ⟨14103696913694293923282293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402464609129529282188195 14103696913694293923282293)
                  ·
                    refine ⟨1322221585658840055307715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14103696913694293923282293 1322221585658840055307715)
                    ·
                      rfl

theorem cell22_3862526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3862526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862526 prefixEnd_3862526 := by exact prefixLift 3862526
  have htrace : WordTrace (prefixWord ++ tailWord_3862526) baseStart_3862526 baseEnd_3862526 := by
    simpa [prefixWord, tailWord_3862526, baseEnd_3862526] using wordTrace_append hprefix tailTrace_3862526
  have hstable : (prefixWord ++ tailWord_3862526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862526).length < 2 ^ (prefixWord ++ tailWord_3862526).sum := by decide
  have hdescent : baseEnd_3862526 < baseStart_3862526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862584 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_3862584 : Nat := 118140960795 + 3862584 * 2 ^ 59
def prefixEnd_3862584 : Nat := 4983230072969 + 3 ^ 40 * 3862584 * 2
def baseEnd_3862584 : Nat := 440747146748049079119179

theorem tailTrace_3862584 : CollatzResearch.WordTrace tailWord_3862584 prefixEnd_3862584 440747146748049079119179 := by
  unfold tailWord_3862584
  simp only [CollatzResearch.WordTrace]
  refine ⟨70440006119262659836377403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93920008159016879781836537 70440006119262659836377403)
  ·
    refine ⟨105660009178893989754566105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70440006119262659836377403 105660009178893989754566105)
    ·
      refine ⟨79245006884170492315924579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105660009178893989754566105 79245006884170492315924579)
      ·
        refine ⟨118867510326255738473886869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79245006884170492315924579 118867510326255738473886869)
        ·
          refine ⟨5571914546543237740963447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118867510326255738473886869 5571914546543237740963447)
          ·
            refine ⟨8357871819814856611445171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571914546543237740963447 8357871819814856611445171)
            ·
              refine ⟨12536807729722284917167757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8357871819814856611445171 12536807729722284917167757)
              ·
                refine ⟨4701302898645856843937909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12536807729722284917167757 4701302898645856843937909)
                ·
                  refine ⟨440747146748049079119179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4701302898645856843937909 440747146748049079119179)
                  ·
                    rfl

theorem cell22_3862584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_3862584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862584 prefixEnd_3862584 := by exact prefixLift 3862584
  have htrace : WordTrace (prefixWord ++ tailWord_3862584) baseStart_3862584 baseEnd_3862584 := by
    simpa [prefixWord, tailWord_3862584, baseEnd_3862584] using wordTrace_append hprefix tailTrace_3862584
  have hstable : (prefixWord ++ tailWord_3862584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862584).length < 2 ^ (prefixWord ++ tailWord_3862584).sum := by decide
  have hdescent : baseEnd_3862584 < baseStart_3862584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862622 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3862622 : Nat := 118140960795 + 3862622 * 2 ^ 59
def prefixEnd_3862622 : Nat := 4983230072969 + 3 ^ 40 * 3862622 * 2
def baseEnd_3862622 : Nat := 1322254448420727804907421

theorem tailTrace_3862622 : CollatzResearch.WordTrace tailWord_3862622 prefixEnd_3862622 1322254448420727804907421 := by
  unfold tailWord_3862622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17610174776548456520329765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93920932141591768108425413 17610174776548456520329765)
  ·
    refine ⟨3301907770602835597561831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17610174776548456520329765 3301907770602835597561831)
    ·
      refine ⟨4952861655904253396342747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301907770602835597561831 4952861655904253396342747)
      ·
        refine ⟨7429292483856380094514121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952861655904253396342747 7429292483856380094514121)
        ·
          refine ⟨5571969362892285070885591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7429292483856380094514121 5571969362892285070885591)
          ·
            refine ⟨8357954044338427606328387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571969362892285070885591 8357954044338427606328387)
            ·
              refine ⟨12536931066507641409492581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8357954044338427606328387 12536931066507641409492581)
              ·
                refine ⟨2350674574970182764279859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12536931066507641409492581 2350674574970182764279859)
                ·
                  refine ⟨3526011862455274146419789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350674574970182764279859 3526011862455274146419789)
                  ·
                    refine ⟨1322254448420727804907421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526011862455274146419789 1322254448420727804907421)
                    ·
                      rfl

theorem cell22_3862622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3862622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862622 prefixEnd_3862622 := by exact prefixLift 3862622
  have htrace : WordTrace (prefixWord ++ tailWord_3862622) baseStart_3862622 baseEnd_3862622 := by
    simpa [prefixWord, tailWord_3862622, baseEnd_3862622] using wordTrace_append hprefix tailTrace_3862622
  have hstable : (prefixWord ++ tailWord_3862622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862622).length < 2 ^ (prefixWord ++ tailWord_3862622).sum := by decide
  have hdescent : baseEnd_3862622 < baseStart_3862622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862659 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 2, 4]
def baseStart_3862659 : Nat := 118140960795 + 3862659 * 2 ^ 59
def prefixEnd_3862659 : Nat := 4983230072969 + 3 ^ 40 * 3862659 * 2
def baseEnd_3862659 : Nat := 1322267114276872041732307

theorem tailTrace_3862659 : CollatzResearch.WordTrace tailWord_3862659 prefixEnd_3862659 1322267114276872041732307 := by
  unfold tailWord_3862659
  simp only [CollatzResearch.WordTrace]
  refine ⟨140882747713253607481735031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93921831808835738321156687 140882747713253607481735031)
  ·
    refine ⟨211324121569880411222602547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140882747713253607481735031 211324121569880411222602547)
    ·
      refine ⟨316986182354820616833903821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211324121569880411222602547 316986182354820616833903821)
      ·
        refine ⟨118869818383057731312713933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316986182354820616833903821 118869818383057731312713933)
        ·
          refine ⟨44576181893646649242267725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118869818383057731312713933 44576181893646649242267725)
          ·
            refine ⟨16716068210117493465850397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44576181893646649242267725 16716068210117493465850397)
            ·
              refine ⟨6268525578794060049693899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16716068210117493465850397 6268525578794060049693899)
              ·
                refine ⟨9402788368191090074540849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268525578794060049693899 9402788368191090074540849)
                ·
                  refine ⟨7052091276143317555905637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9402788368191090074540849 7052091276143317555905637)
                  ·
                    refine ⟨1322267114276872041732307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7052091276143317555905637 1322267114276872041732307)
                    ·
                      rfl

theorem cell22_3862659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].length) (baseStart_3862659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862659 prefixEnd_3862659 := by exact prefixLift 3862659
  have htrace : WordTrace (prefixWord ++ tailWord_3862659) baseStart_3862659 baseEnd_3862659 := by
    simpa [prefixWord, tailWord_3862659, baseEnd_3862659] using wordTrace_append hprefix tailTrace_3862659
  have hstable : (prefixWord ++ tailWord_3862659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862659).length < 2 ^ (prefixWord ++ tailWord_3862659).sum := by decide
  have hdescent : baseEnd_3862659 < baseStart_3862659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862695 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3862695 : Nat := 118140960795 + 3862695 * 2 ^ 59
def prefixEnd_3862695 : Nat := 4983230072969 + 3 ^ 40 * 3862695 * 2
def baseEnd_3862695 : Nat := 1322279437812579947832197

theorem tailTrace_3862695 : CollatzResearch.WordTrace tailWord_3862695 prefixEnd_3862695 1322279437812579947832197 := by
  unfold tailWord_3862695
  simp only [CollatzResearch.WordTrace]
  refine ⟨140884060741123185630045539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93922707160748790420030359 140884060741123185630045539)
  ·
    refine ⟨211326091111684778445068309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140884060741123185630045539 211326091111684778445068309)
    ·
      refine ⟨9905910520860223989612577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211326091111684778445068309 9905910520860223989612577)
      ·
        refine ⟨7429432890645167992209433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9905910520860223989612577 7429432890645167992209433)
        ·
          refine ⟨5572074667983875994157075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7429432890645167992209433 5572074667983875994157075)
          ·
            refine ⟨8358112001975813991235613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572074667983875994157075 8358112001975813991235613)
            ·
              refine ⟨3134292000740930246713355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8358112001975813991235613 3134292000740930246713355)
              ·
                refine ⟨4701438001111395370070033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134292000740930246713355 4701438001111395370070033)
                ·
                  refine ⟨3526078500833546527552525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4701438001111395370070033 3526078500833546527552525)
                  ·
                    refine ⟨1322279437812579947832197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526078500833546527552525 1322279437812579947832197)
                    ·
                      rfl

theorem cell22_3862695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3862695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862695 prefixEnd_3862695 := by exact prefixLift 3862695
  have htrace : WordTrace (prefixWord ++ tailWord_3862695) baseStart_3862695 baseEnd_3862695 := by
    simpa [prefixWord, tailWord_3862695, baseEnd_3862695] using wordTrace_append hprefix tailTrace_3862695
  have hstable : (prefixWord ++ tailWord_3862695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862695).length < 2 ^ (prefixWord ++ tailWord_3862695).sum := by decide
  have hdescent : baseEnd_3862695 < baseStart_3862695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862813 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3862813 : Nat := 118140960795 + 3862813 * 2 ^ 59
def prefixEnd_3862813 : Nat := 4983230072969 + 3 ^ 40 * 3862813 * 2
def baseEnd_3862813 : Nat := 1322319831624066973381835

theorem tailTrace_3862813 : CollatzResearch.WordTrace tailWord_3862813 prefixEnd_3862813 1322319831624066973381835 := by
  unfold tailWord_3862813
  simp only [CollatzResearch.WordTrace]
  refine ⟨140888364554695691782841093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93925576369797127855227395 140888364554695691782841093)
  ·
    refine ⟨26416568354005442209282705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140888364554695691782841093 26416568354005442209282705)
    ·
      refine ⟨19812426265504081656962029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26416568354005442209282705 19812426265504081656962029)
      ·
        refine ⟨7429659849564030621360761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19812426265504081656962029 7429659849564030621360761)
        ·
          refine ⟨5572244887173022966020571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7429659849564030621360761 5572244887173022966020571)
          ·
            refine ⟨8358367330759534449030857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572244887173022966020571 8358367330759534449030857)
            ·
              refine ⟨6268775498069650836773143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8358367330759534449030857 6268775498069650836773143)
              ·
                refine ⟨9403163247104476255159715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268775498069650836773143 9403163247104476255159715)
                ·
                  refine ⟨14104744870656714382739573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9403163247104476255159715 14104744870656714382739573)
                  ·
                    refine ⟨1322319831624066973381835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14104744870656714382739573 1322319831624066973381835)
                    ·
                      rfl

theorem cell22_3862813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3862813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862813 prefixEnd_3862813 := by exact prefixLift 3862813
  have htrace : WordTrace (prefixWord ++ tailWord_3862813) baseStart_3862813 baseEnd_3862813 := by
    simpa [prefixWord, tailWord_3862813, baseEnd_3862813] using wordTrace_append hprefix tailTrace_3862813
  have hstable : (prefixWord ++ tailWord_3862813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862813).length < 2 ^ (prefixWord ++ tailWord_3862813).sum := by decide
  have hdescent : baseEnd_3862813 < baseStart_3862813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862892 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_3862892 : Nat := 118140960795 + 3862892 * 2 ^ 59
def prefixEnd_3862892 : Nat := 4983230072969 + 3 ^ 40 * 3862892 * 2
def baseEnd_3862892 : Nat := 1322346874938537100656593

theorem tailTrace_3862892 : CollatzResearch.WordTrace tailWord_3862892 prefixEnd_3862892 1322346874938537100656593 := by
  unfold tailWord_3862892
  simp only [CollatzResearch.WordTrace]
  refine ⟨70445622960704744137483465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93927497280939658849977953 70445622960704744137483465)
  ·
    refine ⟨52834217220528558103112599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70445622960704744137483465 52834217220528558103112599)
    ·
      refine ⟨79251325830792837154668899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52834217220528558103112599 79251325830792837154668899)
      ·
        refine ⟨118876988746189255732003349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79251325830792837154668899 118876988746189255732003349)
        ·
          refine ⟨5572358847477621362437657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118876988746189255732003349 5572358847477621362437657)
          ·
            refine ⟨4179269135608216021828243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572358847477621362437657 4179269135608216021828243)
            ·
              refine ⟨6268903703412324032742365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179269135608216021828243 6268903703412324032742365)
              ·
                refine ⟨2350838888779621512278387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6268903703412324032742365 2350838888779621512278387)
                ·
                  refine ⟨3526258333169432268417581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350838888779621512278387 3526258333169432268417581)
                  ·
                    refine ⟨1322346874938537100656593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526258333169432268417581 1322346874938537100656593)
                    ·
                      rfl

theorem cell22_3862892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_3862892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862892 prefixEnd_3862892 := by exact prefixLift 3862892
  have htrace : WordTrace (prefixWord ++ tailWord_3862892) baseStart_3862892 baseEnd_3862892 := by
    simpa [prefixWord, tailWord_3862892, baseEnd_3862892] using wordTrace_append hprefix tailTrace_3862892
  have hstable : (prefixWord ++ tailWord_3862892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862892).length < 2 ^ (prefixWord ++ tailWord_3862892).sum := by decide
  have hdescent : baseEnd_3862892 < baseStart_3862892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862922 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_3862922 : Nat := 118140960795 + 3862922 * 2 ^ 59
def prefixEnd_3862922 : Nat := 4983230072969 + 3 ^ 40 * 3862922 * 2
def baseEnd_3862922 : Nat := 440785714850542340802167

theorem tailTrace_3862922 : CollatzResearch.WordTrace tailWord_3862922 prefixEnd_3862922 440785714850542340802167 := by
  unfold tailWord_3862922
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223085027825200849639755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93928226740867202265706013 35223085027825200849639755)
  ·
    refine ⟨52834627541737801274459633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35223085027825200849639755 52834627541737801274459633)
    ·
      refine ⟨39625970656303350955844725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52834627541737801274459633 39625970656303350955844725)
      ·
        refine ⟨3714934749028439152110443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39625970656303350955844725 3714934749028439152110443)
        ·
          refine ⟨5572402123542658728165665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714934749028439152110443 5572402123542658728165665)
          ·
            refine ⟨4179301592656994046124249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572402123542658728165665 4179301592656994046124249)
            ·
              refine ⟨3134476194492745534593187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179301592656994046124249 3134476194492745534593187)
              ·
                refine ⟨4701714291739118301889781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134476194492745534593187 4701714291739118301889781)
                ·
                  refine ⟨440785714850542340802167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4701714291739118301889781 440785714850542340802167)
                  ·
                    rfl

theorem cell22_3862922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_3862922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862922 prefixEnd_3862922 := by exact prefixLift 3862922
  have htrace : WordTrace (prefixWord ++ tailWord_3862922) baseStart_3862922 baseEnd_3862922 := by
    simpa [prefixWord, tailWord_3862922, baseEnd_3862922] using wordTrace_append hprefix tailTrace_3862922
  have hstable : (prefixWord ++ tailWord_3862922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862922).length < 2 ^ (prefixWord ++ tailWord_3862922).sum := by decide
  have hdescent : baseEnd_3862922 < baseStart_3862922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862952 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3862952 : Nat := 118140960795 + 3862952 * 2 ^ 59
def prefixEnd_3862952 : Nat := 4983230072969 + 3 ^ 40 * 3862952 * 2
def baseEnd_3862952 : Nat := 1322367414164716944156409

theorem tailTrace_3862952 : CollatzResearch.WordTrace tailWord_3862952 prefixEnd_3862952 1322367414164716944156409 := by
  unfold tailWord_3862952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70446717150596059261075555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93928956200794745681434073 70446717150596059261075555)
  ·
    refine ⟨105670075725894088891613333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70446717150596059261075555 105670075725894088891613333)
    ·
      refine ⟨4953284799651285416794375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105670075725894088891613333 4953284799651285416794375)
      ·
        refine ⟨7429927199476928125191563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4953284799651285416794375 7429927199476928125191563)
        ·
          refine ⟨11144890799215392187787345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7429927199476928125191563 11144890799215392187787345)
          ·
            refine ⟨8358668099411544140840509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11144890799215392187787345 8358668099411544140840509)
            ·
              refine ⟨3134500537279329052815191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8358668099411544140840509 3134500537279329052815191)
              ·
                refine ⟨4701750805918993579222787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134500537279329052815191 4701750805918993579222787)
                ·
                  refine ⟨7052626208878490368834181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701750805918993579222787 7052626208878490368834181)
                  ·
                    refine ⟨1322367414164716944156409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7052626208878490368834181 1322367414164716944156409)
                    ·
                      rfl

theorem cell22_3862952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3862952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3862952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3862952 prefixEnd_3862952 := by exact prefixLift 3862952
  have htrace : WordTrace (prefixWord ++ tailWord_3862952) baseStart_3862952 baseEnd_3862952 := by
    simpa [prefixWord, tailWord_3862952, baseEnd_3862952] using wordTrace_append hprefix tailTrace_3862952
  have hstable : (prefixWord ++ tailWord_3862952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862952).length < 2 ^ (prefixWord ++ tailWord_3862952).sum := by decide
  have hdescent : baseEnd_3862952 < baseStart_3862952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863265 : List Nat := [1, 2, 3, 1, 4, 2, 2, 7]
def baseStart_3863265 : Nat := 118140960795 + 3863265 * 2 ^ 59
def prefixEnd_3863265 : Nat := 4983230072969 + 3 ^ 40 * 3863265 * 2
def baseEnd_3863265 : Nat := 146941617829032051231161

theorem tailTrace_3863265 : CollatzResearch.WordTrace tailWord_3863265 prefixEnd_3863265 146941617829032051231161 := by
  unfold tailWord_3863265
  simp only [CollatzResearch.WordTrace]
  refine ⟨140904850349058172978295249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93936566899372115318863499 140904850349058172978295249)
  ·
    refine ⟨105678637761793629733721437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140904850349058172978295249 105678637761793629733721437)
    ·
      refine ⟨39629489160672611150145539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105678637761793629733721437 39629489160672611150145539)
      ·
        refine ⟨59444233741008916725218309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39629489160672611150145539 59444233741008916725218309)
        ·
          refine ⟨11145793826439171885978433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59444233741008916725218309 11145793826439171885978433)
          ·
            refine ⟨8359345369829378914483825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11145793826439171885978433 8359345369829378914483825)
            ·
              refine ⟨6269509027372034185862869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8359345369829378914483825 6269509027372034185862869)
              ·
                refine ⟨146941617829032051231161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6269509027372034185862869 146941617829032051231161)
                ·
                  rfl

theorem cell22_3863265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 7].length) (baseStart_3863265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863265 prefixEnd_3863265 := by exact prefixLift 3863265
  have htrace : WordTrace (prefixWord ++ tailWord_3863265) baseStart_3863265 baseEnd_3863265 := by
    simpa [prefixWord, tailWord_3863265, baseEnd_3863265] using wordTrace_append hprefix tailTrace_3863265
  have hstable : (prefixWord ++ tailWord_3863265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863265).length < 2 ^ (prefixWord ++ tailWord_3863265).sum := by decide
  have hdescent : baseEnd_3863265 < baseStart_3863265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863269 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_3863269 : Nat := 118140960795 + 3863269 * 2 ^ 59
def prefixEnd_3863269 : Nat := 4983230072969 + 3 ^ 40 * 3863269 * 2
def baseEnd_3863269 : Nat := 1322475929743033783980437

theorem tailTrace_3863269 : CollatzResearch.WordTrace tailWord_3863269 prefixEnd_3863269 1322475929743033783980437 := by
  unfold tailWord_3863269
  simp only [CollatzResearch.WordTrace]
  refine ⟨140904996241043681661440861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93936664160695787774293907 140904996241043681661440861)
  ·
    refine ⟨52839373590391380623040323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140904996241043681661440861 52839373590391380623040323)
    ·
      refine ⟨79259060385587070934560485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52839373590391380623040323 79259060385587070934560485)
      ·
        refine ⟨14861073822297575800230091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79259060385587070934560485 14861073822297575800230091)
        ·
          refine ⟨22291610733446363700345137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14861073822297575800230091 22291610733446363700345137)
          ·
            refine ⟨16718708050084772775258853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22291610733446363700345137 16718708050084772775258853)
            ·
              refine ⟨3134757759390894895361035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16718708050084772775258853 3134757759390894895361035)
              ·
                refine ⟨4702136639086342343041553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134757759390894895361035 4702136639086342343041553)
                ·
                  refine ⟨3526602479314756757281165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702136639086342343041553 3526602479314756757281165)
                  ·
                    refine ⟨1322475929743033783980437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526602479314756757281165 1322475929743033783980437)
                    ·
                      rfl

theorem cell22_3863269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_3863269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863269 prefixEnd_3863269 := by exact prefixLift 3863269
  have htrace : WordTrace (prefixWord ++ tailWord_3863269) baseStart_3863269 baseEnd_3863269 := by
    simpa [prefixWord, tailWord_3863269, baseEnd_3863269] using wordTrace_append hprefix tailTrace_3863269
  have hstable : (prefixWord ++ tailWord_3863269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863269).length < 2 ^ (prefixWord ++ tailWord_3863269).sum := by decide
  have hdescent : baseEnd_3863269 < baseStart_3863269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863280 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_3863280 : Nat := 118140960795 + 3863280 * 2 ^ 59
def prefixEnd_3863280 : Nat := 4983230072969 + 3 ^ 40 * 3863280 * 2
def baseEnd_3863280 : Nat := 1322479695267833421955403

theorem tailTrace_3863280 : CollatzResearch.WordTrace tailWord_3863280 prefixEnd_3863280 1322479695267833421955403 := by
  unfold tailWord_3863280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70452698722001915270045647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93936931629335887026727529 70452698722001915270045647)
  ·
    refine ⟨105679048083002872905068471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70452698722001915270045647 105679048083002872905068471)
    ·
      refine ⟨158518572124504309357602707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105679048083002872905068471 158518572124504309357602707)
      ·
        refine ⟨237777858186756464036404061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158518572124504309357602707 237777858186756464036404061)
        ·
          refine ⟨89166696820033674013651523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237777858186756464036404061 89166696820033674013651523)
          ·
            refine ⟨133750045230050511020477285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89166696820033674013651523 133750045230050511020477285)
            ·
              refine ⟨25078133480634470816339491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133750045230050511020477285 25078133480634470816339491)
              ·
                refine ⟨37617200220951706224509237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25078133480634470816339491 37617200220951706224509237)
                ·
                  refine ⟨3526612520714222458547741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37617200220951706224509237 3526612520714222458547741)
                  ·
                    refine ⟨1322479695267833421955403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526612520714222458547741 1322479695267833421955403)
                    ·
                      rfl

theorem cell22_3863280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_3863280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863280 prefixEnd_3863280 := by exact prefixLift 3863280
  have htrace : WordTrace (prefixWord ++ tailWord_3863280) baseStart_3863280 baseEnd_3863280 := by
    simpa [prefixWord, tailWord_3863280, baseEnd_3863280] using wordTrace_append hprefix tailTrace_3863280
  have hstable : (prefixWord ++ tailWord_3863280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863280).length < 2 ^ (prefixWord ++ tailWord_3863280).sum := by decide
  have hdescent : baseEnd_3863280 < baseStart_3863280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863323 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_3863323 : Nat := 118140960795 + 3863323 * 2 ^ 59
def prefixEnd_3863323 : Nat := 4983230072969 + 3 ^ 40 * 3863323 * 2
def baseEnd_3863323 : Nat := 1322494415046595643130271

theorem tailTrace_3863323 : CollatzResearch.WordTrace tailWord_3863323 prefixEnd_3863323 1322494415046595643130271 := by
  unfold tailWord_3863323
  simp only [CollatzResearch.WordTrace]
  refine ⟨140906965782848048883906623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93937977188565365922604415 140906965782848048883906623)
  ·
    refine ⟨211360448674272073325859935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140906965782848048883906623 211360448674272073325859935)
    ·
      refine ⟨317040673011408109988789903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211360448674272073325859935 317040673011408109988789903)
      ·
        refine ⟨475561009517112164983184855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317040673011408109988789903 475561009517112164983184855)
        ·
          refine ⟨713341514275668247474777283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475561009517112164983184855 713341514275668247474777283)
          ·
            refine ⟨1070012271413502371212165925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713341514275668247474777283 1070012271413502371212165925)
            ·
              refine ⟨200627300890031694602281111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1070012271413502371212165925 200627300890031694602281111)
              ·
                refine ⟨300940951335047541903421667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200627300890031694602281111 300940951335047541903421667)
                ·
                  refine ⟨451411427002571312855132501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300940951335047541903421667 451411427002571312855132501)
                  ·
                    refine ⟨1322494415046595643130271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 451411427002571312855132501 1322494415046595643130271)
                    ·
                      rfl

theorem cell22_3863323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_3863323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863323 prefixEnd_3863323 := by exact prefixLift 3863323
  have htrace : WordTrace (prefixWord ++ tailWord_3863323) baseStart_3863323 baseEnd_3863323 := by
    simpa [prefixWord, tailWord_3863323, baseEnd_3863323] using wordTrace_append hprefix tailTrace_3863323
  have hstable : (prefixWord ++ tailWord_3863323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863323).length < 2 ^ (prefixWord ++ tailWord_3863323).sum := by decide
  have hdescent : baseEnd_3863323 < baseStart_3863323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863340 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_3863340 : Nat := 118140960795 + 3863340 * 2 ^ 59
def prefixEnd_3863340 : Nat := 4983230072969 + 3 ^ 40 * 3863340 * 2
def baseEnd_3863340 : Nat := 1322500234494013265455219

theorem tailTrace_3863340 : CollatzResearch.WordTrace tailWord_3863340 prefixEnd_3863340 1322500234494013265455219 := by
  unfold tailWord_3863340
  simp only [CollatzResearch.WordTrace]
  refine ⟨70453792911893230393637737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93938390549190973858183649 70453792911893230393637737)
  ·
    refine ⟨52840344683919922795228303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70453792911893230393637737 52840344683919922795228303)
    ·
      refine ⟨79260517025879884192842455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52840344683919922795228303 79260517025879884192842455)
      ·
        refine ⟨118890775538819826289263683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79260517025879884192842455 118890775538819826289263683)
        ·
          refine ⟨178336163308229739433895525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118890775538819826289263683 178336163308229739433895525)
          ·
            refine ⟨33438030620293076143855411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178336163308229739433895525 33438030620293076143855411)
            ·
              refine ⟨50157045930439614215783117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33438030620293076143855411 50157045930439614215783117)
              ·
                refine ⟨18808892223914855330918669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50157045930439614215783117 18808892223914855330918669)
                ·
                  refine ⟨7053334583968070749094501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18808892223914855330918669 7053334583968070749094501)
                  ·
                    refine ⟨1322500234494013265455219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7053334583968070749094501 1322500234494013265455219)
                    ·
                      rfl

theorem cell22_3863340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_3863340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863340 prefixEnd_3863340 := by exact prefixLift 3863340
  have htrace : WordTrace (prefixWord ++ tailWord_3863340) baseStart_3863340 baseEnd_3863340 := by
    simpa [prefixWord, tailWord_3863340, baseEnd_3863340] using wordTrace_append hprefix tailTrace_3863340
  have hstable : (prefixWord ++ tailWord_3863340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863340).length < 2 ^ (prefixWord ++ tailWord_3863340).sum := by decide
  have hdescent : baseEnd_3863340 < baseStart_3863340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863348 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_3863348 : Nat := 118140960795 + 3863348 * 2 ^ 59
def prefixEnd_3863348 : Nat := 4983230072969 + 3 ^ 40 * 3863348 * 2
def baseEnd_3863348 : Nat := 1322502973057503911255195

theorem tailTrace_3863348 : CollatzResearch.WordTrace tailWord_3863348 prefixEnd_3863348 1322502973057503911255195 := by
  unfold tailWord_3863348
  simp only [CollatzResearch.WordTrace]
  refine ⟨70453938803878739076783349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93938585071838318769044465 70453938803878739076783349)
  ·
    refine ⟨6605056762863631788448439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70453938803878739076783349 6605056762863631788448439)
    ·
      refine ⟨9907585144295447682672659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6605056762863631788448439 9907585144295447682672659)
      ·
        refine ⟨14861377716443171524008989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907585144295447682672659 14861377716443171524008989)
        ·
          refine ⟨5573016643666189321503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14861377716443171524008989 5573016643666189321503371)
          ·
            refine ⟨8359524965499283982255057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573016643666189321503371 8359524965499283982255057)
            ·
              refine ⟨6269643724124462986691293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8359524965499283982255057 6269643724124462986691293)
              ·
                refine ⟨2351116396546673620009235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6269643724124462986691293 2351116396546673620009235)
                ·
                  refine ⟨3526674594820010430013853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351116396546673620009235 3526674594820010430013853)
                  ·
                    refine ⟨1322502973057503911255195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526674594820010430013853 1322502973057503911255195)
                    ·
                      rfl

theorem cell22_3863348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_3863348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863348 prefixEnd_3863348 := by exact prefixLift 3863348
  have htrace : WordTrace (prefixWord ++ tailWord_3863348) baseStart_3863348 baseEnd_3863348 := by
    simpa [prefixWord, tailWord_3863348, baseEnd_3863348] using wordTrace_append hprefix tailTrace_3863348
  have hstable : (prefixWord ++ tailWord_3863348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863348).length < 2 ^ (prefixWord ++ tailWord_3863348).sum := by decide
  have hdescent : baseEnd_3863348 < baseStart_3863348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863361 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 5]
def baseStart_3863361 : Nat := 118140960795 + 3863361 * 2 ^ 59
def prefixEnd_3863361 : Nat := 4983230072969 + 3 ^ 40 * 3863361 * 2
def baseEnd_3863361 : Nat := 440835807741058736893385

theorem tailTrace_3863361 : CollatzResearch.WordTrace tailWord_3863361 prefixEnd_3863361 440835807741058736893385 := by
  unfold tailWord_3863361
  simp only [CollatzResearch.WordTrace]
  refine ⟨140908351756710381373789937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93938901171140254249193291 140908351756710381373789937)
  ·
    refine ⟨105681263817532786030342453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140908351756710381373789937 105681263817532786030342453)
    ·
      refine ⟨9907618482893698690344605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105681263817532786030342453 9907618482893698690344605)
      ·
        refine ⟨3715356931085137008879227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9907618482893698690344605 3715356931085137008879227)
        ·
          refine ⟨5573035396627705513318841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715356931085137008879227 5573035396627705513318841)
          ·
            refine ⟨4179776547470779134989131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5573035396627705513318841 4179776547470779134989131)
            ·
              refine ⟨6269664821206168702483697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179776547470779134989131 6269664821206168702483697)
              ·
                refine ⟨4702248615904626526862773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6269664821206168702483697 4702248615904626526862773)
                ·
                  refine ⟨440835807741058736893385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4702248615904626526862773 440835807741058736893385)
                  ·
                    rfl

theorem cell22_3863361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_3863361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863361 prefixEnd_3863361 := by exact prefixLift 3863361
  have htrace : WordTrace (prefixWord ++ tailWord_3863361) baseStart_3863361 baseEnd_3863361 := by
    simpa [prefixWord, tailWord_3863361, baseEnd_3863361] using wordTrace_append hprefix tailTrace_3863361
  have hstable : (prefixWord ++ tailWord_3863361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863361).length < 2 ^ (prefixWord ++ tailWord_3863361).sum := by decide
  have hdescent : baseEnd_3863361 < baseStart_3863361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863372 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_3863372 : Nat := 118140960795 + 3863372 * 2 ^ 59
def prefixEnd_3863372 : Nat := 4983230072969 + 3 ^ 40 * 3863372 * 2
def baseEnd_3863372 : Nat := 440837062915991949551707

theorem tailTrace_3863372 : CollatzResearch.WordTrace tailWord_3863372 prefixEnd_3863372 440837062915991949551707 := by
  unfold tailWord_3863372
  simp only [CollatzResearch.WordTrace]
  refine ⟨70454376479835265126220185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93939168639780353501626913 70454376479835265126220185)
  ·
    refine ⟨52840782359876448844665139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70454376479835265126220185 52840782359876448844665139)
    ·
      refine ⟨79261173539814673266997709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52840782359876448844665139 79261173539814673266997709)
      ·
        refine ⟨29722940077430502475124141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79261173539814673266997709 29722940077430502475124141)
        ·
          refine ⟨11146102529036438428171553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29722940077430502475124141 11146102529036438428171553)
          ·
            refine ⟨8359576896777328821128665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11146102529036438428171553 8359576896777328821128665)
            ·
              refine ⟨6269682672582996615846499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8359576896777328821128665 6269682672582996615846499)
              ·
                refine ⟨9404524008874494923769749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269682672582996615846499 9404524008874494923769749)
                ·
                  refine ⟨440837062915991949551707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9404524008874494923769749 440837062915991949551707)
                  ·
                    rfl

theorem cell22_3863372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_3863372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863372 prefixEnd_3863372 := by exact prefixLift 3863372
  have htrace : WordTrace (prefixWord ++ tailWord_3863372) baseStart_3863372 baseEnd_3863372 := by
    simpa [prefixWord, tailWord_3863372, baseEnd_3863372] using wordTrace_append hprefix tailTrace_3863372
  have hstable : (prefixWord ++ tailWord_3863372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863372).length < 2 ^ (prefixWord ++ tailWord_3863372).sum := by decide
  have hdescent : baseEnd_3863372 < baseStart_3863372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863385 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_3863385 : Nat := 118140960795 + 3863385 * 2 ^ 59
def prefixEnd_3863385 : Nat := 4983230072969 + 3 ^ 40 * 3863385 * 2
def baseEnd_3863385 : Nat := 1322515638913648148080081

theorem tailTrace_3863385 : CollatzResearch.WordTrace tailWord_3863385 prefixEnd_3863385 1322515638913648148080081 := by
  unfold tailWord_3863385
  simp only [CollatzResearch.WordTrace]
  refine ⟨140909227108623433472663609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93939484739082288981775739 140909227108623433472663609)
  ·
    refine ⟨105681920331467575104497707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140909227108623433472663609 105681920331467575104497707)
    ·
      refine ⟨158522880497201362656746561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105681920331467575104497707 158522880497201362656746561)
      ·
        refine ⟨118892160372901021992559921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158522880497201362656746561 118892160372901021992559921)
        ·
          refine ⟨89169120279675766494419941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118892160372901021992559921 89169120279675766494419941)
          ·
            refine ⟨16719210052439206217703739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89169120279675766494419941 16719210052439206217703739)
            ·
              refine ⟨25078815078658809326555609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16719210052439206217703739 25078815078658809326555609)
              ·
                refine ⟨18809111308994106994916707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25078815078658809326555609 18809111308994106994916707)
                ·
                  refine ⟨28213666963491160492375061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18809111308994106994916707 28213666963491160492375061)
                  ·
                    refine ⟨1322515638913648148080081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28213666963491160492375061 1322515638913648148080081)
                    ·
                      rfl

theorem cell22_3863385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_3863385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863385 prefixEnd_3863385 := by exact prefixLift 3863385
  have htrace : WordTrace (prefixWord ++ tailWord_3863385) baseStart_3863385 baseEnd_3863385 := by
    simpa [prefixWord, tailWord_3863385, baseEnd_3863385] using wordTrace_append hprefix tailTrace_3863385
  have hstable : (prefixWord ++ tailWord_3863385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863385).length < 2 ^ (prefixWord ++ tailWord_3863385).sum := by decide
  have hdescent : baseEnd_3863385 < baseStart_3863385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863477 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3863477 : Nat := 118140960795 + 3863477 * 2 ^ 59
def prefixEnd_3863477 : Nat := 4983230072969 + 3 ^ 40 * 3863477 * 2
def baseEnd_3863477 : Nat := 1322547132393790574779799

theorem tailTrace_3863477 : CollatzResearch.WordTrace tailWord_3863477 prefixEnd_3863477 1322547132393790574779799 := by
  unfold tailWord_3863477
  simp only [CollatzResearch.WordTrace]
  refine ⟨140912582624290133185012685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93941721749526755456675123 140912582624290133185012685)
  ·
    refine ⟨52842218484108799944379757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140912582624290133185012685 52842218484108799944379757)
    ·
      refine ⟨19815831931540799979142409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52842218484108799944379757 19815831931540799979142409)
      ·
        refine ⟨14861873948655599984356807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19815831931540799979142409 14861873948655599984356807)
        ·
          refine ⟨22292810922983399976535211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14861873948655599984356807 22292810922983399976535211)
          ·
            refine ⟨33439216384475099964802817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22292810922983399976535211 33439216384475099964802817)
            ·
              refine ⟨25079412288356324973602113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33439216384475099964802817 25079412288356324973602113)
              ·
                refine ⟨18809559216267243730201585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25079412288356324973602113 18809559216267243730201585)
                ·
                  refine ⟨14107169412200432797651189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18809559216267243730201585 14107169412200432797651189)
                  ·
                    refine ⟨1322547132393790574779799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14107169412200432797651189 1322547132393790574779799)
                    ·
                      rfl

theorem cell22_3863477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3863477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863477 prefixEnd_3863477 := by exact prefixLift 3863477
  have htrace : WordTrace (prefixWord ++ tailWord_3863477) baseStart_3863477 baseEnd_3863477 := by
    simpa [prefixWord, tailWord_3863477, baseEnd_3863477] using wordTrace_append hprefix tailTrace_3863477
  have hstable : (prefixWord ++ tailWord_3863477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863477).length < 2 ^ (prefixWord ++ tailWord_3863477).sum := by decide
  have hdescent : baseEnd_3863477 < baseStart_3863477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863642 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_3863642 : Nat := 118140960795 + 3863642 * 2 ^ 59
def prefixEnd_3863642 : Nat := 4983230072969 + 3 ^ 40 * 3863642 * 2
def baseEnd_3863642 : Nat := 440867871755261714801431

theorem tailTrace_3863642 : CollatzResearch.WordTrace tailWord_3863642 prefixEnd_3863642 440867871755261714801431 := by
  unfold tailWord_3863642
  simp only [CollatzResearch.WordTrace]
  refine ⟨35229650167173091591192295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93945733779128244243179453 35229650167173091591192295)
  ·
    refine ⟨52844475250759637386788443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35229650167173091591192295 52844475250759637386788443)
    ·
      refine ⟨79266712876139456080182665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52844475250759637386788443 79266712876139456080182665)
      ·
        refine ⟨59450034657104592060136999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79266712876139456080182665 59450034657104592060136999)
        ·
          refine ⟨89175051985656888090205499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59450034657104592060136999 89175051985656888090205499)
          ·
            refine ⟨133762577978485332135308249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89175051985656888090205499 133762577978485332135308249)
            ·
              refine ⟨100321933483863999101481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133762577978485332135308249 100321933483863999101481187)
              ·
                refine ⟨150482900225795998652221781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100321933483863999101481187 150482900225795998652221781)
                ·
                  refine ⟨440867871755261714801431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150482900225795998652221781 440867871755261714801431)
                  ·
                    rfl

theorem cell22_3863642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_3863642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863642 prefixEnd_3863642 := by exact prefixLift 3863642
  have htrace : WordTrace (prefixWord ++ tailWord_3863642) baseStart_3863642 baseEnd_3863642 := by
    simpa [prefixWord, tailWord_3863642, baseEnd_3863642] using wordTrace_append hprefix tailTrace_3863642
  have hstable : (prefixWord ++ tailWord_3863642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863642).length < 2 ^ (prefixWord ++ tailWord_3863642).sum := by decide
  have hdescent : baseEnd_3863642 < baseStart_3863642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863689 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_3863689 : Nat := 118140960795 + 3863689 * 2 ^ 59
def prefixEnd_3863689 : Nat := 4983230072969 + 3 ^ 40 * 3863689 * 2
def baseEnd_3863689 : Nat := 1322619704326292688479149

theorem tailTrace_3863689 : CollatzResearch.WordTrace tailWord_3863689 prefixEnd_3863689 1322619704326292688479149 := by
  unfold tailWord_3863689
  simp only [CollatzResearch.WordTrace]
  refine ⟨140920314899522093391730121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93946876599681395594486747 140920314899522093391730121)
  ·
    refine ⟨105690236174641570043797591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140920314899522093391730121 105690236174641570043797591)
    ·
      refine ⟨158535354261962355065696387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105690236174641570043797591 158535354261962355065696387)
      ·
        refine ⟨237803031392943532598544581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158535354261962355065696387 237803031392943532598544581)
        ·
          refine ⟨44588068386176912362227109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237803031392943532598544581 44588068386176912362227109)
          ·
            refine ⟨8360262822408171067917583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44588068386176912362227109 8360262822408171067917583)
            ·
              refine ⟨12540394233612256601876375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360262822408171067917583 12540394233612256601876375)
              ·
                refine ⟨18810591350418384902814563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12540394233612256601876375 18810591350418384902814563)
                ·
                  refine ⟨28215887025627577354221845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18810591350418384902814563 28215887025627577354221845)
                  ·
                    refine ⟨1322619704326292688479149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28215887025627577354221845 1322619704326292688479149)
                    ·
                      rfl

theorem cell22_3863689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_3863689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863689 prefixEnd_3863689 := by exact prefixLift 3863689
  have htrace : WordTrace (prefixWord ++ tailWord_3863689) baseStart_3863689 baseEnd_3863689 := by
    simpa [prefixWord, tailWord_3863689, baseEnd_3863689] using wordTrace_append hprefix tailTrace_3863689
  have hstable : (prefixWord ++ tailWord_3863689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863689).length < 2 ^ (prefixWord ++ tailWord_3863689).sum := by decide
  have hdescent : baseEnd_3863689 < baseStart_3863689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863704 : List Nat := [2, 1, 2, 4, 2, 2, 9]
def baseStart_3863704 : Nat := 118140960795 + 3863704 * 2 ^ 59
def prefixEnd_3863704 : Nat := 4983230072969 + 3 ^ 40 * 3863704 * 2
def baseEnd_3863704 : Nat := 48986105153068061087189

theorem tailTrace_3863704 : CollatzResearch.WordTrace tailWord_3863704 prefixEnd_3863704 48986105153068061087189 := by
  unfold tailWord_3863704
  simp only [CollatzResearch.WordTrace]
  refine ⟨70460430997233875476763083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93947241329645167302350777 70460430997233875476763083)
  ·
    refine ⟨105690646495850813215144625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70460430997233875476763083 105690646495850813215144625)
    ·
      refine ⟨79267984871888109911358469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105690646495850813215144625 79267984871888109911358469)
      ·
        refine ⟨14862747163479020608379713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79267984871888109911358469 14862747163479020608379713)
        ·
          refine ⟨11147060372609265456284785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14862747163479020608379713 11147060372609265456284785)
          ·
            refine ⟨8360295279456949092213589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11147060372609265456284785 8360295279456949092213589)
            ·
              refine ⟨48986105153068061087189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8360295279456949092213589 48986105153068061087189)
              ·
                rfl

theorem cell22_3863704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 9].length) (baseStart_3863704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863704 prefixEnd_3863704 := by exact prefixLift 3863704
  have htrace : WordTrace (prefixWord ++ tailWord_3863704) baseStart_3863704 baseEnd_3863704 := by
    simpa [prefixWord, tailWord_3863704, baseEnd_3863704] using wordTrace_append hprefix tailTrace_3863704
  have hstable : (prefixWord ++ tailWord_3863704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863704).length < 2 ^ (prefixWord ++ tailWord_3863704).sum := by decide
  have hdescent : baseEnd_3863704 < baseStart_3863704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863708 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3863708 : Nat := 118140960795 + 3863708 * 2 ^ 59
def prefixEnd_3863708 : Nat := 4983230072969 + 3 ^ 40 * 3863708 * 2
def baseEnd_3863708 : Nat := 1322626208414582972254091

theorem tailTrace_3863708 : CollatzResearch.WordTrace tailWord_3863708 prefixEnd_3863708 1322626208414582972254091 := by
  unfold tailWord_3863708
  simp only [CollatzResearch.WordTrace]
  refine ⟨70460503943226629818335889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93947338590968839757781185 70460503943226629818335889)
  ·
    refine ⟨52845377957419972363751917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70460503943226629818335889 52845377957419972363751917)
    ·
      refine ⟨19817016734032489636406969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52845377957419972363751917 19817016734032489636406969)
      ·
        refine ⟨14862762550524367227305227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19817016734032489636406969 14862762550524367227305227)
        ·
          refine ⟨22294143825786550840957841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14862762550524367227305227 22294143825786550840957841)
          ·
            refine ⟨16720607869339913130718381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22294143825786550840957841 16720607869339913130718381)
            ·
              refine ⟨6270227951002467424019393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16720607869339913130718381 6270227951002467424019393)
              ·
                refine ⟨4702670963251850568014545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270227951002467424019393 4702670963251850568014545)
                ·
                  refine ⟨3527003222438887926010909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702670963251850568014545 3527003222438887926010909)
                  ·
                    refine ⟨1322626208414582972254091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527003222438887926010909 1322626208414582972254091)
                    ·
                      rfl

theorem cell22_3863708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3863708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863708 prefixEnd_3863708 := by exact prefixLift 3863708
  have htrace : WordTrace (prefixWord ++ tailWord_3863708) baseStart_3863708 baseEnd_3863708 := by
    simpa [prefixWord, tailWord_3863708, baseEnd_3863708] using wordTrace_append hprefix tailTrace_3863708
  have hstable : (prefixWord ++ tailWord_3863708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863708).length < 2 ^ (prefixWord ++ tailWord_3863708).sum := by decide
  have hdescent : baseEnd_3863708 < baseStart_3863708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863725 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3863725 : Nat := 118140960795 + 3863725 * 2 ^ 59
def prefixEnd_3863725 : Nat := 4983230072969 + 3 ^ 40 * 3863725 * 2
def baseEnd_3863725 : Nat := 1322632027862000594579039

theorem tailTrace_3863725 : CollatzResearch.WordTrace tailWord_3863725 prefixEnd_3863725 1322632027862000594579039 := by
  unfold tailWord_3863725
  simp only [CollatzResearch.WordTrace]
  refine ⟨140921627927391671540040629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93947751951594447693360419 140921627927391671540040629)
  ·
    refine ⟨13211402618192969206878809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140921627927391671540040629 13211402618192969206878809)
    ·
      refine ⟨9908551963644726905159107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13211402618192969206878809 9908551963644726905159107)
      ·
        refine ⟨14862827945467090357738661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9908551963644726905159107 14862827945467090357738661)
        ·
          refine ⟨2786780239775079442075999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14862827945467090357738661 2786780239775079442075999)
          ·
            refine ⟨4180170359662619163113999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786780239775079442075999 4180170359662619163113999)
            ·
              refine ⟨6270255539493928744670999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180170359662619163113999 6270255539493928744670999)
              ·
                refine ⟨9405383309240893117006499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270255539493928744670999 9405383309240893117006499)
                ·
                  refine ⟨14108074963861339675509749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9405383309240893117006499 14108074963861339675509749)
                  ·
                    refine ⟨1322632027862000594579039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14108074963861339675509749 1322632027862000594579039)
                    ·
                      rfl

theorem cell22_3863725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3863725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863725 prefixEnd_3863725 := by exact prefixLift 3863725
  have htrace : WordTrace (prefixWord ++ tailWord_3863725) baseStart_3863725 baseEnd_3863725 := by
    simpa [prefixWord, tailWord_3863725, baseEnd_3863725] using wordTrace_append hprefix tailTrace_3863725
  have hstable : (prefixWord ++ tailWord_3863725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863725).length < 2 ^ (prefixWord ++ tailWord_3863725).sum := by decide
  have hdescent : baseEnd_3863725 < baseStart_3863725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863783 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 5]
def baseStart_3863783 : Nat := 118140960795 + 3863783 * 2 ^ 59
def prefixEnd_3863783 : Nat := 4983230072969 + 3 ^ 40 * 3863783 * 2
def baseEnd_3863783 : Nat := 440883960815769258876287

theorem tailTrace_3863783 : CollatzResearch.WordTrace tailWord_3863783 prefixEnd_3863783 440883960815769258876287 := by
  unfold tailWord_3863783
  simp only [CollatzResearch.WordTrace]
  refine ⟨140923743361181547445652003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93949162240787698297101335 140923743361181547445652003)
  ·
    refine ⟨211385615041772321168478005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140923743361181547445652003 211385615041772321168478005)
    ·
      refine ⟨19817401410166155109544813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211385615041772321168478005 19817401410166155109544813)
      ·
        refine ⟨7431525528812308166079305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19817401410166155109544813 7431525528812308166079305)
        ·
          refine ⟨5573644146609231124559479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7431525528812308166079305 5573644146609231124559479)
          ·
            refine ⟨8360466219913846686839219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573644146609231124559479 8360466219913846686839219)
            ·
              refine ⟨12540699329870770030258829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360466219913846686839219 12540699329870770030258829)
              ·
                refine ⟨4702762248701538761347061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12540699329870770030258829 4702762248701538761347061)
                ·
                  refine ⟨440883960815769258876287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4702762248701538761347061 440883960815769258876287)
                  ·
                    rfl

theorem cell22_3863783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 5].length) (baseStart_3863783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863783 prefixEnd_3863783 := by exact prefixLift 3863783
  have htrace : WordTrace (prefixWord ++ tailWord_3863783) baseStart_3863783 baseEnd_3863783 := by
    simpa [prefixWord, tailWord_3863783, baseEnd_3863783] using wordTrace_append hprefix tailTrace_3863783
  have hstable : (prefixWord ++ tailWord_3863783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863783).length < 2 ^ (prefixWord ++ tailWord_3863783).sum := by decide
  have hdescent : baseEnd_3863783 < baseStart_3863783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863813 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_3863813 : Nat := 118140960795 + 3863813 * 2 ^ 59
def prefixEnd_3863813 : Nat := 4983230072969 + 3 ^ 40 * 3863813 * 2
def baseEnd_3863813 : Nat := 1322662152060397698378769

theorem tailTrace_3863813 : CollatzResearch.WordTrace tailWord_3863813 prefixEnd_3863813 1322662152060397698378769 := by
  unfold tailWord_3863813
  simp only [CollatzResearch.WordTrace]
  refine ⟨140924837551072862569244093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93949891700715241712829395 140924837551072862569244093)
  ·
    refine ⟨52846814081652323463466535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140924837551072862569244093 52846814081652323463466535)
    ·
      refine ⟨79270221122478485195199803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52846814081652323463466535 79270221122478485195199803)
      ·
        refine ⟨118905331683717727792799705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79270221122478485195199803 118905331683717727792799705)
        ·
          refine ⟨89178998762788295844599779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118905331683717727792799705 89178998762788295844599779)
          ·
            refine ⟨133768498144182443766899669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89178998762788295844599779 133768498144182443766899669)
            ·
              refine ⟨3135199175254276025786711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133768498144182443766899669 3135199175254276025786711)
              ·
                refine ⟨4702798762881414038680067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135199175254276025786711 4702798762881414038680067)
                ·
                  refine ⟨7054198144322121058020101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702798762881414038680067 7054198144322121058020101)
                  ·
                    refine ⟨1322662152060397698378769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054198144322121058020101 1322662152060397698378769)
                    ·
                      rfl

theorem cell22_3863813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_3863813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863813 prefixEnd_3863813 := by exact prefixLift 3863813
  have htrace : WordTrace (prefixWord ++ tailWord_3863813) baseStart_3863813 baseEnd_3863813 := by
    simpa [prefixWord, tailWord_3863813, baseEnd_3863813] using wordTrace_append hprefix tailTrace_3863813
  have hstable : (prefixWord ++ tailWord_3863813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863813).length < 2 ^ (prefixWord ++ tailWord_3863813).sum := by decide
  have hdescent : baseEnd_3863813 < baseStart_3863813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863843 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 2, 3]
def baseStart_3863843 : Nat := 118140960795 + 3863843 * 2 ^ 59
def prefixEnd_3863843 : Nat := 4983230072969 + 3 ^ 40 * 3863843 * 2
def baseEnd_3863843 : Nat := 1322672421673487620128677

theorem tailTrace_3863843 : CollatzResearch.WordTrace tailWord_3863843 prefixEnd_3863843 1322672421673487620128677 := by
  unfold tailWord_3863843
  simp only [CollatzResearch.WordTrace]
  refine ⟨140925931740964177692836183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93950621160642785128557455 140925931740964177692836183)
  ·
    refine ⟨211388897611446266539254275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140925931740964177692836183 211388897611446266539254275)
    ·
      refine ⟨317083346417169399808881413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211388897611446266539254275 317083346417169399808881413)
      ·
        refine ⟨59453127453219262464165265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317083346417169399808881413 59453127453219262464165265)
        ·
          refine ⟨44589845589914446848123949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59453127453219262464165265 44589845589914446848123949)
          ·
            refine ⟨16721192096217917568046481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44589845589914446848123949 16721192096217917568046481)
            ·
              refine ⟨12540894072163438176034861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16721192096217917568046481 12540894072163438176034861)
              ·
                refine ⟨4702835277061289316013073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12540894072163438176034861 4702835277061289316013073)
                ·
                  refine ⟨3527126457795966987009805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702835277061289316013073 3527126457795966987009805)
                  ·
                    refine ⟨1322672421673487620128677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527126457795966987009805 1322672421673487620128677)
                    ·
                      rfl

theorem cell22_3863843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 3].length) (baseStart_3863843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863843 prefixEnd_3863843 := by exact prefixLift 3863843
  have htrace : WordTrace (prefixWord ++ tailWord_3863843) baseStart_3863843 baseEnd_3863843 := by
    simpa [prefixWord, tailWord_3863843, baseEnd_3863843] using wordTrace_append hprefix tailTrace_3863843
  have hstable : (prefixWord ++ tailWord_3863843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863843).length < 2 ^ (prefixWord ++ tailWord_3863843).sum := by decide
  have hdescent : baseEnd_3863843 < baseStart_3863843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863856 : List Nat := [2, 1, 1, 1, 2, 2, 7, 6]
def baseStart_3863856 : Nat := 118140960795 + 3863856 * 2 ^ 59
def prefixEnd_3863856 : Nat := 4983230072969 + 3 ^ 40 * 3863856 * 2
def baseEnd_3863856 : Nat := 146964096871017768839293

theorem tailTrace_3863856 : CollatzResearch.WordTrace tailWord_3863856 prefixEnd_3863856 146964096871017768839293 := by
  unfold tailWord_3863856
  simp only [CollatzResearch.WordTrace]
  refine ⟨70463202944958540456529711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93950937259944720608706281 70463202944958540456529711)
  ·
    refine ⟨105694804417437810684794567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70463202944958540456529711 105694804417437810684794567)
    ·
      refine ⟨158542206626156716027191851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105694804417437810684794567 158542206626156716027191851)
      ·
        refine ⟨237813309939235074040787777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158542206626156716027191851 237813309939235074040787777)
        ·
          refine ⟨178359982454426305530590833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237813309939235074040787777 178359982454426305530590833)
          ·
            refine ⟨133769986840819729147943125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178359982454426305530590833 133769986840819729147943125)
            ·
              refine ⟨3135234066581712401904917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133769986840819729147943125 3135234066581712401904917)
              ·
                refine ⟨146964096871017768839293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3135234066581712401904917 146964096871017768839293)
                ·
                  rfl

theorem cell22_3863856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_3863856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863856 prefixEnd_3863856 := by exact prefixLift 3863856
  have htrace : WordTrace (prefixWord ++ tailWord_3863856) baseStart_3863856 baseEnd_3863856 := by
    simpa [prefixWord, tailWord_3863856, baseEnd_3863856] using wordTrace_append hprefix tailTrace_3863856
  have hstable : (prefixWord ++ tailWord_3863856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863856).length < 2 ^ (prefixWord ++ tailWord_3863856).sum := by decide
  have hdescent : baseEnd_3863856 < baseStart_3863856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863858 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_3863858 : Nat := 118140960795 + 3863858 * 2 ^ 59
def prefixEnd_3863858 : Nat := 4983230072969 + 3 ^ 40 * 3863858 * 2
def baseEnd_3863858 : Nat := 1322677556480032581003631

theorem tailTrace_3863858 : CollatzResearch.WordTrace tailWord_3863858 prefixEnd_3863858 1322677556480032581003631 := by
  unfold tailWord_3863858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35231619708977458813658057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93950985890606556836421485 35231619708977458813658057)
  ·
    refine ⟨26423714781733094110243543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35231619708977458813658057 26423714781733094110243543)
    ·
      refine ⟨39635572172599641165365315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26423714781733094110243543 39635572172599641165365315)
      ·
        refine ⟨59453358258899461748047973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39635572172599641165365315 59453358258899461748047973)
        ·
          refine ⟨11147504673543649077758995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59453358258899461748047973 11147504673543649077758995)
          ·
            refine ⟨16721257010315473616638493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11147504673543649077758995 16721257010315473616638493)
            ·
              refine ⟨6270471378868302606239435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16721257010315473616638493 6270471378868302606239435)
              ·
                refine ⟨9405707068302453909359153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270471378868302606239435 9405707068302453909359153)
                ·
                  refine ⟨7054280301226840432019365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9405707068302453909359153 7054280301226840432019365)
                  ·
                    refine ⟨1322677556480032581003631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054280301226840432019365 1322677556480032581003631)
                    ·
                      rfl

theorem cell22_3863858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_3863858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863858 prefixEnd_3863858 := by exact prefixLift 3863858
  have htrace : WordTrace (prefixWord ++ tailWord_3863858) baseStart_3863858 baseEnd_3863858 := by
    simpa [prefixWord, tailWord_3863858, baseEnd_3863858] using wordTrace_append hprefix tailTrace_3863858
  have hstable : (prefixWord ++ tailWord_3863858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863858).length < 2 ^ (prefixWord ++ tailWord_3863858).sum := by decide
  have hdescent : baseEnd_3863858 < baseStart_3863858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863888 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_3863888 : Nat := 118140960795 + 3863888 * 2 ^ 59
def prefixEnd_3863888 : Nat := 4983230072969 + 3 ^ 40 * 3863888 * 2
def baseEnd_3863888 : Nat := 1322687826093122502753539

theorem tailTrace_3863888 : CollatzResearch.WordTrace tailWord_3863888 prefixEnd_3863888 1322687826093122502753539 := by
  unfold tailWord_3863888
  simp only [CollatzResearch.WordTrace]
  refine ⟨70463786512900575189112159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93951715350534100252149545 70463786512900575189112159)
  ·
    refine ⟨105695679769350862783668239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70463786512900575189112159 105695679769350862783668239)
    ·
      refine ⟨158543519654026294175502359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105695679769350862783668239 158543519654026294175502359)
      ·
        refine ⟨237815279481039441263253539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158543519654026294175502359 237815279481039441263253539)
        ·
          refine ⟨356722919221559161894880309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237815279481039441263253539 356722919221559161894880309)
          ·
            refine ⟨33442773677021171427645029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356722919221559161894880309 33442773677021171427645029)
            ·
              refine ⟨6270520064441469642683443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33442773677021171427645029 6270520064441469642683443)
              ·
                refine ⟨9405780096662204464025165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270520064441469642683443 9405780096662204464025165)
                ·
                  refine ⟨3527167536248326674009437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9405780096662204464025165 3527167536248326674009437)
                  ·
                    refine ⟨1322687826093122502753539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527167536248326674009437 1322687826093122502753539)
                    ·
                      rfl

theorem cell22_3863888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_3863888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863888 prefixEnd_3863888 := by exact prefixLift 3863888
  have htrace : WordTrace (prefixWord ++ tailWord_3863888) baseStart_3863888 baseEnd_3863888 := by
    simpa [prefixWord, tailWord_3863888, baseEnd_3863888] using wordTrace_append hprefix tailTrace_3863888
  have hstable : (prefixWord ++ tailWord_3863888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863888).length < 2 ^ (prefixWord ++ tailWord_3863888).sum := by decide
  have hdescent : baseEnd_3863888 < baseStart_3863888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863965 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3863965 : Nat := 118140960795 + 3863965 * 2 ^ 59
def prefixEnd_3863965 : Nat := 4983230072969 + 3 ^ 40 * 3863965 * 2
def baseEnd_3863965 : Nat := 1322714184766719968578303

theorem tailTrace_3863965 : CollatzResearch.WordTrace tailWord_3863965 prefixEnd_3863965 1322714184766719968578303 := by
  unfold tailWord_3863965
  simp only [CollatzResearch.WordTrace]
  refine ⟨140930381446522192528777349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93953587631014795019184899 140930381446522192528777349)
  ·
    refine ⟨26424446521222911099145753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140930381446522192528777349 26424446521222911099145753)
    ·
      refine ⟨19818334890917183324359315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26424446521222911099145753 19818334890917183324359315)
      ·
        refine ⟨29727502336375774986538973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19818334890917183324359315 29727502336375774986538973)
        ·
          refine ⟨11147813376140915619952115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29727502336375774986538973 11147813376140915619952115)
          ·
            refine ⟨16721720064211373429928173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11147813376140915619952115 16721720064211373429928173)
            ·
              refine ⟨6270645024079265036223065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16721720064211373429928173 6270645024079265036223065)
              ·
                refine ⟨4702983768059448777167299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270645024079265036223065 4702983768059448777167299)
                ·
                  refine ⟨7054475652089173165750949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702983768059448777167299 7054475652089173165750949)
                  ·
                    refine ⟨1322714184766719968578303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054475652089173165750949 1322714184766719968578303)
                    ·
                      rfl

theorem cell22_3863965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3863965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3863965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3863965 prefixEnd_3863965 := by exact prefixLift 3863965
  have htrace : WordTrace (prefixWord ++ tailWord_3863965) baseStart_3863965 baseEnd_3863965 := by
    simpa [prefixWord, tailWord_3863965, baseEnd_3863965] using wordTrace_append hprefix tailTrace_3863965
  have hstable : (prefixWord ++ tailWord_3863965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863965).length < 2 ^ (prefixWord ++ tailWord_3863965).sum := by decide
  have hdescent : baseEnd_3863965 < baseStart_3863965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864098 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_3864098 : Nat := 118140960795 + 3864098 * 2 ^ 59
def prefixEnd_3864098 : Nat := 4983230072969 + 3 ^ 40 * 3864098 * 2
def baseEnd_3864098 : Nat := 440919904461583985000965

theorem tailTrace_3864098 : CollatzResearch.WordTrace tailWord_3864098 prefixEnd_3864098 440919904461583985000965 := by
  unfold tailWord_3864098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35233808088760089060842237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93956821570026904162245965 35233808088760089060842237)
  ·
    refine ⟨13212678033285033397815839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35233808088760089060842237 13212678033285033397815839)
    ·
      refine ⟨19819017049927550096723759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13212678033285033397815839 19819017049927550096723759)
      ·
        refine ⟨29728525574891325145085639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19819017049927550096723759 29728525574891325145085639)
        ·
          refine ⟨44592788362336987717628459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29728525574891325145085639 44592788362336987717628459)
          ·
            refine ⟨66889182543505481576442689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44592788362336987717628459 66889182543505481576442689)
            ·
              refine ⟨50166886907629111182332017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66889182543505481576442689 50166886907629111182332017)
              ·
                refine ⟨37625165180721833386749013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50166886907629111182332017 37625165180721833386749013)
                ·
                  refine ⟨440919904461583985000965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37625165180721833386749013 440919904461583985000965)
                  ·
                    rfl

theorem cell22_3864098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_3864098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864098 prefixEnd_3864098 := by exact prefixLift 3864098
  have htrace : WordTrace (prefixWord ++ tailWord_3864098) baseStart_3864098 baseEnd_3864098 := by
    simpa [prefixWord, tailWord_3864098, baseEnd_3864098] using wordTrace_append hprefix tailTrace_3864098
  have hstable : (prefixWord ++ tailWord_3864098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864098).length < 2 ^ (prefixWord ++ tailWord_3864098).sum := by decide
  have hdescent : baseEnd_3864098 < baseStart_3864098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864115 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 6]
def baseStart_3864115 : Nat := 118140960795 + 3864115 * 2 ^ 59
def prefixEnd_3864115 : Nat := 4983230072969 + 3 ^ 40 * 3864115 * 2
def baseEnd_3864115 : Nat := 440921844277389859109281

theorem tailTrace_3864115 : CollatzResearch.WordTrace tailWord_3864115 prefixEnd_3864115 440921844277389859109281 := by
  unfold tailWord_3864115
  simp only [CollatzResearch.WordTrace]
  refine ⟨140935852395978768146737799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93957234930652512097825199 140935852395978768146737799)
  ·
    refine ⟨211403778593968152220106699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140935852395978768146737799 211403778593968152220106699)
    ·
      refine ⟨317105667890952228330160049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211403778593968152220106699 317105667890952228330160049)
      ·
        refine ⟨237829250918214171247620037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317105667890952228330160049 237829250918214171247620037)
        ·
          refine ⟨44592984547165157108928757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237829250918214171247620037 44592984547165157108928757)
          ·
            refine ⟨4180592301296733478962071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44592984547165157108928757 4180592301296733478962071)
            ·
              refine ⟨6270888451945100218443107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180592301296733478962071 6270888451945100218443107)
              ·
                refine ⟨9406332677917650327664661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270888451945100218443107 9406332677917650327664661)
                ·
                  refine ⟨440921844277389859109281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9406332677917650327664661 440921844277389859109281)
                  ·
                    rfl

theorem cell22_3864115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 6].length) (baseStart_3864115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864115 prefixEnd_3864115 := by exact prefixLift 3864115
  have htrace : WordTrace (prefixWord ++ tailWord_3864115) baseStart_3864115 baseEnd_3864115 := by
    simpa [prefixWord, tailWord_3864115, baseEnd_3864115] using wordTrace_append hprefix tailTrace_3864115
  have hstable : (prefixWord ++ tailWord_3864115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864115).length < 2 ^ (prefixWord ++ tailWord_3864115).sum := by decide
  have hdescent : baseEnd_3864115 < baseStart_3864115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864128 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_3864128 : Nat := 118140960795 + 3864128 * 2 ^ 59
def prefixEnd_3864128 : Nat := 4983230072969 + 3 ^ 40 * 3864128 * 2
def baseEnd_3864128 : Nat := 1322769982997841876752803

theorem tailTrace_3864128 : CollatzResearch.WordTrace tailWord_3864128 prefixEnd_3864128 1322769982997841876752803 := by
  unfold tailWord_3864128
  simp only [CollatzResearch.WordTrace]
  refine ⟨70468163272465835683480519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93957551029954447577974025 70468163272465835683480519)
  ·
    refine ⟨105702244908698753525220779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70468163272465835683480519 105702244908698753525220779)
    ·
      refine ⟨158553367363048130287831169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105702244908698753525220779 158553367363048130287831169)
      ·
        refine ⟨118915025522286097715873377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158553367363048130287831169 118915025522286097715873377)
        ·
          refine ⟨89186269141714573286905033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118915025522286097715873377 89186269141714573286905033)
          ·
            refine ⟨66889701856285929965178775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89186269141714573286905033 66889701856285929965178775)
            ·
              refine ⟨100334552784428894947768163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66889701856285929965178775 100334552784428894947768163)
              ·
                refine ⟨150501829176643342421652245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100334552784428894947768163 150501829176643342421652245)
                ·
                  refine ⟨7054773242655156676014949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150501829176643342421652245 7054773242655156676014949)
                  ·
                    refine ⟨1322769982997841876752803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054773242655156676014949 1322769982997841876752803)
                    ·
                      rfl

theorem cell22_3864128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_3864128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864128 prefixEnd_3864128 := by exact prefixLift 3864128
  have htrace : WordTrace (prefixWord ++ tailWord_3864128) baseStart_3864128 baseEnd_3864128 := by
    simpa [prefixWord, tailWord_3864128, baseEnd_3864128] using wordTrace_append hprefix tailTrace_3864128
  have hstable : (prefixWord ++ tailWord_3864128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864128).length < 2 ^ (prefixWord ++ tailWord_3864128).sum := by decide
  have hdescent : baseEnd_3864128 < baseStart_3864128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864134 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3864134 : Nat := 118140960795 + 3864134 * 2 ^ 59
def prefixEnd_3864134 : Nat := 4983230072969 + 3 ^ 40 * 3864134 * 2
def baseEnd_3864134 : Nat := 1322772036920459861102785

theorem tailTrace_3864134 : CollatzResearch.WordTrace tailWord_3864134 prefixEnd_3864134 1322772036920459861102785 := by
  unfold tailWord_3864134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404267043215935449739983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93957696921939956261119637 4404267043215935449739983)
  ·
    refine ⟨6606400564823903174609975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4404267043215935449739983 6606400564823903174609975)
    ·
      refine ⟨9909600847235854761914963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606400564823903174609975 9909600847235854761914963)
      ·
        refine ⟨14864401270853782142872445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9909600847235854761914963 14864401270853782142872445)
        ·
          refine ⟨5574150476570168303577167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14864401270853782142872445 5574150476570168303577167)
          ·
            refine ⟨8361225714855252455365751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574150476570168303577167 8361225714855252455365751)
            ·
              refine ⟨12541838572282878683048627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8361225714855252455365751 12541838572282878683048627)
              ·
                refine ⟨18812757858424318024572941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12541838572282878683048627 18812757858424318024572941)
                ·
                  refine ⟨7054784196909119259214853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18812757858424318024572941 7054784196909119259214853)
                  ·
                    refine ⟨1322772036920459861102785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054784196909119259214853 1322772036920459861102785)
                    ·
                      rfl

theorem cell22_3864134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3864134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864134 prefixEnd_3864134 := by exact prefixLift 3864134
  have htrace : WordTrace (prefixWord ++ tailWord_3864134) baseStart_3864134 baseEnd_3864134 := by
    simpa [prefixWord, tailWord_3864134, baseEnd_3864134] using wordTrace_append hprefix tailTrace_3864134
  have hstable : (prefixWord ++ tailWord_3864134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864134).length < 2 ^ (prefixWord ++ tailWord_3864134).sum := by decide
  have hdescent : baseEnd_3864134 < baseStart_3864134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864145 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_3864145 : Nat := 118140960795 + 3864145 * 2 ^ 59
def prefixEnd_3864145 : Nat := 4983230072969 + 3 ^ 40 * 3864145 * 2
def baseEnd_3864145 : Nat := 1322775802445259499077751

theorem tailTrace_3864145 : CollatzResearch.WordTrace tailWord_3864145 prefixEnd_3864145 1322775802445259499077751 := by
  unfold tailWord_3864145
  simp only [CollatzResearch.WordTrace]
  refine ⟨140936946585870083270329889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93957964390580055513553259 140936946585870083270329889)
  ·
    refine ⟨105702709939402562452747417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140936946585870083270329889 105702709939402562452747417)
    ·
      refine ⟨79277032454551921839560563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105702709939402562452747417 79277032454551921839560563)
      ·
        refine ⟨118915548681827882759340845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79277032454551921839560563 118915548681827882759340845)
        ·
          refine ⟨44593330755685456034752817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118915548681827882759340845 44593330755685456034752817)
          ·
            refine ⟨33444998066764092026064613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44593330755685456034752817 33444998066764092026064613)
            ·
              refine ⟨6270937137518267254887115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33444998066764092026064613 6270937137518267254887115)
              ·
                refine ⟨9406405706277400882330673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270937137518267254887115 9406405706277400882330673)
                ·
                  refine ⟨7054804279708050661748005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9406405706277400882330673 7054804279708050661748005)
                  ·
                    refine ⟨1322775802445259499077751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054804279708050661748005 1322775802445259499077751)
                    ·
                      rfl

theorem cell22_3864145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_3864145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864145 prefixEnd_3864145 := by exact prefixLift 3864145
  have htrace : WordTrace (prefixWord ++ tailWord_3864145) baseStart_3864145 baseEnd_3864145 := by
    simpa [prefixWord, tailWord_3864145, baseEnd_3864145] using wordTrace_append hprefix tailTrace_3864145
  have hstable : (prefixWord ++ tailWord_3864145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864145).length < 2 ^ (prefixWord ++ tailWord_3864145).sum := by decide
  have hdescent : baseEnd_3864145 < baseStart_3864145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864175 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 3, 3]
def baseStart_3864175 : Nat := 118140960795 + 3864175 * 2 ^ 59
def prefixEnd_3864175 : Nat := 4983230072969 + 3 ^ 40 * 3864175 * 2
def baseEnd_3864175 : Nat := 1322786072058349420827659

theorem tailTrace_3864175 : CollatzResearch.WordTrace tailWord_3864175 prefixEnd_3864175 1322786072058349420827659 := by
  unfold tailWord_3864175
  simp only [CollatzResearch.WordTrace]
  refine ⟨140938040775761398393921979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93958693850507598929281319 140938040775761398393921979)
  ·
    refine ⟨211407061163642097590882969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140938040775761398393921979 211407061163642097590882969)
    ·
      refine ⟨158555295872731573193162227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211407061163642097590882969 158555295872731573193162227)
      ·
        refine ⟨237832943809097359789743341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158555295872731573193162227 237832943809097359789743341)
        ·
          refine ⟨89187353928411509921153753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237832943809097359789743341 89187353928411509921153753)
          ·
            refine ⟨66890515446308632440865315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89187353928411509921153753 66890515446308632440865315)
            ·
              refine ⟨100335773169462948661297973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66890515446308632440865315 100335773169462948661297973)
              ·
                refine ⟨9406478734637151436996685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100335773169462948661297973 9406478734637151436996685)
                ·
                  refine ⟨3527429525488931788873757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9406478734637151436996685 3527429525488931788873757)
                  ·
                    refine ⟨1322786072058349420827659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527429525488931788873757 1322786072058349420827659)
                    ·
                      rfl

theorem cell22_3864175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_3864175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864175 prefixEnd_3864175 := by exact prefixLift 3864175
  have htrace : WordTrace (prefixWord ++ tailWord_3864175) baseStart_3864175 baseEnd_3864175 := by
    simpa [prefixWord, tailWord_3864175, baseEnd_3864175] using wordTrace_append hprefix tailTrace_3864175
  have hstable : (prefixWord ++ tailWord_3864175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864175).length < 2 ^ (prefixWord ++ tailWord_3864175).sum := by decide
  have hdescent : baseEnd_3864175 < baseStart_3864175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864188 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_3864188 : Nat := 118140960795 + 3864188 * 2 ^ 59
def prefixEnd_3864188 : Nat := 4983230072969 + 3 ^ 40 * 3864188 * 2
def baseEnd_3864188 : Nat := 440930174074673906750873

theorem tailTrace_3864188 : CollatzResearch.WordTrace tailWord_3864188 prefixEnd_3864188 440930174074673906750873 := by
  unfold tailWord_3864188
  simp only [CollatzResearch.WordTrace]
  refine ⟨70469257462357150807072609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93959009949809534409430145 70469257462357150807072609)
  ·
    refine ⟨52851943096767863105304457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70469257462357150807072609 52851943096767863105304457)
    ·
      refine ⟨39638957322575897328978343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52851943096767863105304457 39638957322575897328978343)
      ·
        refine ⟨59458435983863845993467515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39638957322575897328978343 59458435983863845993467515)
        ·
          refine ⟨89187653975795768990201273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59458435983863845993467515 89187653975795768990201273)
          ·
            refine ⟨66890740481846826742650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89187653975795768990201273 66890740481846826742650955)
            ·
              refine ⟨100336110722770240113976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66890740481846826742650955 100336110722770240113976433)
              ·
                refine ⟨75252083042077680085482325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100336110722770240113976433 75252083042077680085482325)
                ·
                  refine ⟨440930174074673906750873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75252083042077680085482325 440930174074673906750873)
                  ·
                    rfl

theorem cell22_3864188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_3864188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864188 prefixEnd_3864188 := by exact prefixLift 3864188
  have htrace : WordTrace (prefixWord ++ tailWord_3864188) baseStart_3864188 baseEnd_3864188 := by
    simpa [prefixWord, tailWord_3864188, baseEnd_3864188] using wordTrace_append hprefix tailTrace_3864188
  have hstable : (prefixWord ++ tailWord_3864188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864188).length < 2 ^ (prefixWord ++ tailWord_3864188).sum := by decide
  have hdescent : baseEnd_3864188 < baseStart_3864188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864203 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_3864203 : Nat := 118140960795 + 3864203 * 2 ^ 59
def prefixEnd_3864203 : Nat := 4983230072969 + 3 ^ 40 * 3864203 * 2
def baseEnd_3864203 : Nat := 1322795657030566681127573

theorem tailTrace_3864203 : CollatzResearch.WordTrace tailWord_3864203 prefixEnd_3864203 1322795657030566681127573 := by
  unfold tailWord_3864203
  simp only [CollatzResearch.WordTrace]
  refine ⟨140939062019659959175941263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93959374679773306117294175 140939062019659959175941263)
  ·
    refine ⟨211408593029489938763911895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140939062019659959175941263 211408593029489938763911895)
    ·
      refine ⟨317112889544234908145867843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211408593029489938763911895 317112889544234908145867843)
      ·
        refine ⟨475669334316352362218801765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317112889544234908145867843 475669334316352362218801765)
        ·
          refine ⟨89188000184316067916025331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475669334316352362218801765 89188000184316067916025331)
          ·
            refine ⟨133782000276474101874037997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89188000184316067916025331 133782000276474101874037997)
            ·
              refine ⟨50168250103677788202764249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133782000276474101874037997 50168250103677788202764249)
              ·
                refine ⟨37626187577758341152073187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50168250103677788202764249 37626187577758341152073187)
                ·
                  refine ⟨56439281366637511728109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37626187577758341152073187 56439281366637511728109781)
                  ·
                    refine ⟨1322795657030566681127573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56439281366637511728109781 1322795657030566681127573)
                    ·
                      rfl

theorem cell22_3864203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_3864203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864203 prefixEnd_3864203 := by exact prefixLift 3864203
  have htrace : WordTrace (prefixWord ++ tailWord_3864203) baseStart_3864203 baseEnd_3864203 := by
    simpa [prefixWord, tailWord_3864203, baseEnd_3864203] using wordTrace_append hprefix tailTrace_3864203
  have hstable : (prefixWord ++ tailWord_3864203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864203).length < 2 ^ (prefixWord ++ tailWord_3864203).sum := by decide
  have hdescent : baseEnd_3864203 < baseStart_3864203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864222 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3864222 : Nat := 118140960795 + 3864222 * 2 ^ 59
def prefixEnd_3864222 : Nat := 4983230072969 + 3 ^ 40 * 3864222 * 2
def baseEnd_3864222 : Nat := 440934053706285654967505

theorem tailTrace_3864222 : CollatzResearch.WordTrace tailWord_3864222 prefixEnd_3864222 440934053706285654967505 := by
  unfold tailWord_3864222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17617469375823890677610365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93959836671060750280588613 17617469375823890677610365)
  ·
    refine ⟨6606551015933959004103887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17617469375823890677610365 6606551015933959004103887)
    ·
      refine ⟨9909826523900938506155831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606551015933959004103887 9909826523900938506155831)
      ·
        refine ⟨14864739785851407759233747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9909826523900938506155831 14864739785851407759233747)
        ·
          refine ⟨22297109678777111638850621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14864739785851407759233747 22297109678777111638850621)
          ·
            refine ⟨8361416129541416864568983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22297109678777111638850621 8361416129541416864568983)
            ·
              refine ⟨12542124194312125296853475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8361416129541416864568983 12542124194312125296853475)
              ·
                refine ⟨18813186291468187945280213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12542124194312125296853475 18813186291468187945280213)
                ·
                  refine ⟨440934053706285654967505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18813186291468187945280213 440934053706285654967505)
                  ·
                    rfl

theorem cell22_3864222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3864222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864222 prefixEnd_3864222 := by exact prefixLift 3864222
  have htrace : WordTrace (prefixWord ++ tailWord_3864222) baseStart_3864222 baseEnd_3864222 := by
    simpa [prefixWord, tailWord_3864222, baseEnd_3864222] using wordTrace_append hprefix tailTrace_3864222
  have hstable : (prefixWord ++ tailWord_3864222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864222).length < 2 ^ (prefixWord ++ tailWord_3864222).sum := by decide
  have hdescent : baseEnd_3864222 < baseStart_3864222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864226 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3864226 : Nat := 118140960795 + 3864226 * 2 ^ 59
def prefixEnd_3864226 : Nat := 4983230072969 + 3 ^ 40 * 3864226 * 2
def baseEnd_3864226 : Nat := 1322803530400602287802503

theorem tailTrace_3864226 : CollatzResearch.WordTrace tailWord_3864226 prefixEnd_3864226 1322803530400602287802503 := by
  unfold tailWord_3864226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35234975224644158526007133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93959933932384422736019021 35234975224644158526007133)
  ·
    refine ⟨13213115709241559447252675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35234975224644158526007133 13213115709241559447252675)
    ·
      refine ⟨19819673563862339170879013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13213115709241559447252675 19819673563862339170879013)
      ·
        refine ⟨3716188793224188594539815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19819673563862339170879013 3716188793224188594539815)
        ·
          refine ⟨5574283189836282891809723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716188793224188594539815 5574283189836282891809723)
          ·
            refine ⟨8361424784754424337714585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574283189836282891809723 8361424784754424337714585)
            ·
              refine ⟨6271068588565818253285939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8361424784754424337714585 6271068588565818253285939)
              ·
                refine ⟨9406602882848727379928909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271068588565818253285939 9406602882848727379928909)
                ·
                  refine ⟨3527476081068272767473341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9406602882848727379928909 3527476081068272767473341)
                  ·
                    refine ⟨1322803530400602287802503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527476081068272767473341 1322803530400602287802503)
                    ·
                      rfl

theorem cell22_3864226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3864226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864226 prefixEnd_3864226 := by exact prefixLift 3864226
  have htrace : WordTrace (prefixWord ++ tailWord_3864226) baseStart_3864226 baseEnd_3864226 := by
    simpa [prefixWord, tailWord_3864226, baseEnd_3864226] using wordTrace_append hprefix tailTrace_3864226
  have hstable : (prefixWord ++ tailWord_3864226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864226).length < 2 ^ (prefixWord ++ tailWord_3864226).sum := by decide
  have hdescent : baseEnd_3864226 < baseStart_3864226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864250 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_3864250 : Nat := 118140960795 + 3864250 * 2 ^ 59
def prefixEnd_3864250 : Nat := 4983230072969 + 3 ^ 40 * 3864250 * 2
def baseEnd_3864250 : Nat := 440937248697024741734143

theorem tailTrace_3864250 : CollatzResearch.WordTrace tailWord_3864250 prefixEnd_3864250 440937248697024741734143 := by
  unfold tailWord_3864250
  simp only [CollatzResearch.WordTrace]
  refine ⟨35235194062622421550725551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93960517500326457468601469 35235194062622421550725551)
  ·
    refine ⟨52852791093933632326088327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35235194062622421550725551 52852791093933632326088327)
    ·
      refine ⟨79279186640900448489132491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52852791093933632326088327 79279186640900448489132491)
      ·
        refine ⟨118918779961350672733698737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79279186640900448489132491 118918779961350672733698737)
        ·
          refine ⟨89189084971013004550274053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118918779961350672733698737 89189084971013004550274053)
          ·
            refine ⟨16722953432064938353176385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89189084971013004550274053 16722953432064938353176385)
            ·
              refine ⟨12542215074048703764882289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16722953432064938353176385 12542215074048703764882289)
              ·
                refine ⟨9406661305536527823661717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12542215074048703764882289 9406661305536527823661717)
                ·
                  refine ⟨440937248697024741734143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9406661305536527823661717 440937248697024741734143)
                  ·
                    rfl

theorem cell22_3864250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_3864250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864250 prefixEnd_3864250 := by exact prefixLift 3864250
  have htrace : WordTrace (prefixWord ++ tailWord_3864250) baseStart_3864250 baseEnd_3864250 := by
    simpa [prefixWord, tailWord_3864250, baseEnd_3864250] using wordTrace_append hprefix tailTrace_3864250
  have hstable : (prefixWord ++ tailWord_3864250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864250).length < 2 ^ (prefixWord ++ tailWord_3864250).sum := by decide
  have hdescent : baseEnd_3864250 < baseStart_3864250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864252 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_3864252 : Nat := 118140960795 + 3864252 * 2 ^ 59
def prefixEnd_3864252 : Nat := 4983230072969 + 3 ^ 40 * 3864252 * 2
def baseEnd_3864252 : Nat := 1322812430731946886652423

theorem tailTrace_3864252 : CollatzResearch.WordTrace tailWord_3864252 prefixEnd_3864252 1322812430731946886652423 := by
  unfold tailWord_3864252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70470424598241220272237505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93960566130988293696316673 70470424598241220272237505)
  ·
    refine ⟨52852818448680915204178129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70470424598241220272237505 52852818448680915204178129)
    ·
      refine ⟨39639613836510686403133597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52852818448680915204178129 39639613836510686403133597)
      ·
        refine ⟨14864855188691507401175099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39639613836510686403133597 14864855188691507401175099)
        ·
          refine ⟨22297282783037261101762649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14864855188691507401175099 22297282783037261101762649)
          ·
            refine ⟨16722962087277945826321987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22297282783037261101762649 16722962087277945826321987)
            ·
              refine ⟨25084443130916918739482981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16722962087277945826321987 25084443130916918739482981)
              ·
                refine ⟨4703333087046922263653059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25084443130916918739482981 4703333087046922263653059)
                ·
                  refine ⟨7054999630570383395479589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703333087046922263653059 7054999630570383395479589)
                  ·
                    refine ⟨1322812430731946886652423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054999630570383395479589 1322812430731946886652423)
                    ·
                      rfl

theorem cell22_3864252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_3864252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864252 prefixEnd_3864252 := by exact prefixLift 3864252
  have htrace : WordTrace (prefixWord ++ tailWord_3864252) baseStart_3864252 baseEnd_3864252 := by
    simpa [prefixWord, tailWord_3864252, baseEnd_3864252] using wordTrace_append hprefix tailTrace_3864252
  have hstable : (prefixWord ++ tailWord_3864252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864252).length < 2 ^ (prefixWord ++ tailWord_3864252).sum := by decide
  have hdescent : baseEnd_3864252 < baseStart_3864252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864282 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_3864282 : Nat := 118140960795 + 3864282 * 2 ^ 59
def prefixEnd_3864282 : Nat := 4983230072969 + 3 ^ 40 * 3864282 * 2
def baseEnd_3864282 : Nat := 1322822700345036808402331

theorem tailTrace_3864282 : CollatzResearch.WordTrace tailWord_3864282 prefixEnd_3864282 1322822700345036808402331 := by
  unfold tailWord_3864282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35235485846593438917016775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93961295590915837112044733 35235485846593438917016775)
  ·
    refine ⟨52853228769890158375525163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35235485846593438917016775 52853228769890158375525163)
    ·
      refine ⟨79279843154835237563287745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52853228769890158375525163 79279843154835237563287745)
      ·
        refine ⟨59459882366126428172465809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79279843154835237563287745 59459882366126428172465809)
        ·
          refine ⟨44594911774594821129349357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59459882366126428172465809 44594911774594821129349357)
          ·
            refine ⟨16723091915473057923506009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44594911774594821129349357 16723091915473057923506009)
            ·
              refine ⟨12542318936604793442629507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16723091915473057923506009 12542318936604793442629507)
              ·
                refine ⟨18813478404907190163944261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12542318936604793442629507 18813478404907190163944261)
                ·
                  refine ⟨3527527200920098155739549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18813478404907190163944261 3527527200920098155739549)
                  ·
                    refine ⟨1322822700345036808402331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527527200920098155739549 1322822700345036808402331)
                    ·
                      rfl

theorem cell22_3864282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_3864282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864282 prefixEnd_3864282 := by exact prefixLift 3864282
  have htrace : WordTrace (prefixWord ++ tailWord_3864282) baseStart_3864282 baseEnd_3864282 := by
    simpa [prefixWord, tailWord_3864282, baseEnd_3864282] using wordTrace_append hprefix tailTrace_3864282
  have hstable : (prefixWord ++ tailWord_3864282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864282).length < 2 ^ (prefixWord ++ tailWord_3864282).sum := by decide
  have hdescent : baseEnd_3864282 < baseStart_3864282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864299 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 2, 3]
def baseStart_3864299 : Nat := 118140960795 + 3864299 * 2 ^ 59
def prefixEnd_3864299 : Nat := 4983230072969 + 3 ^ 40 * 3864299 * 2
def baseEnd_3864299 : Nat := 1322828519792454430727279

theorem tailTrace_3864299 : CollatzResearch.WordTrace tailWord_3864299 prefixEnd_3864299 1322828519792454430727279 := by
  unfold tailWord_3864299
  simp only [CollatzResearch.WordTrace]
  refine ⟨140942563427312167571435951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93961708951541445047623967 140942563427312167571435951)
  ·
    refine ⟨211413845140968251357153927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140942563427312167571435951 211413845140968251357153927)
    ·
      refine ⟨317120767711452377035730891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211413845140968251357153927 317120767711452377035730891)
      ·
        refine ⟨475681151567178565553596337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317120767711452377035730891 475681151567178565553596337)
        ·
          refine ⟨356760863675383924165197253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475681151567178565553596337 356760863675383924165197253)
          ·
            refine ⟨66892661939134485780974485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356760863675383924165197253 66892661939134485780974485)
            ·
              refine ⟨3135593528396929020983179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66892661939134485780974485 3135593528396929020983179)
              ·
                refine ⟨4703390292595393531474769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135593528396929020983179 4703390292595393531474769)
                ·
                  refine ⟨3527542719446545148606077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703390292595393531474769 3527542719446545148606077)
                  ·
                    refine ⟨1322828519792454430727279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527542719446545148606077 1322828519792454430727279)
                    ·
                      rfl

theorem cell22_3864299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 3].length) (baseStart_3864299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864299 prefixEnd_3864299 := by exact prefixLift 3864299
  have htrace : WordTrace (prefixWord ++ tailWord_3864299) baseStart_3864299 baseEnd_3864299 := by
    simpa [prefixWord, tailWord_3864299, baseEnd_3864299] using wordTrace_append hprefix tailTrace_3864299
  have hstable : (prefixWord ++ tailWord_3864299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864299).length < 2 ^ (prefixWord ++ tailWord_3864299).sum := by decide
  have hdescent : baseEnd_3864299 < baseStart_3864299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864355 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_3864355 : Nat := 118140960795 + 3864355 * 2 ^ 59
def prefixEnd_3864355 : Nat := 4983230072969 + 3 ^ 40 * 3864355 * 2
def baseEnd_3864355 : Nat := 1322847689736888951327107

theorem tailTrace_3864355 : CollatzResearch.WordTrace tailWord_3864355 prefixEnd_3864355 1322847689736888951327107 := by
  unfold tailWord_3864355
  simp only [CollatzResearch.WordTrace]
  refine ⟨140944605915109289135474519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93963070610072859423649679 140944605915109289135474519)
  ·
    refine ⟨211416908872663933703211779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140944605915109289135474519 211416908872663933703211779)
    ·
      refine ⟨317125363308995900554817669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211416908872663933703211779 317125363308995900554817669)
      ·
        refine ⟨59461005620436731354028313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317125363308995900554817669 59461005620436731354028313)
        ·
          refine ⟨44595754215327548515521235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59461005620436731354028313 44595754215327548515521235)
          ·
            refine ⟨66893631322991322773281853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44595754215327548515521235 66893631322991322773281853)
            ·
              refine ⟨25085111746121746039980695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66893631322991322773281853 25085111746121746039980695)
              ·
                refine ⟨37627667619182619059971043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25085111746121746039980695 37627667619182619059971043)
                ·
                  refine ⟨56441501428773928589956565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37627667619182619059971043 56441501428773928589956565)
                  ·
                    refine ⟨1322847689736888951327107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56441501428773928589956565 1322847689736888951327107)
                    ·
                      rfl

theorem cell22_3864355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_3864355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864355 prefixEnd_3864355 := by exact prefixLift 3864355
  have htrace : WordTrace (prefixWord ++ tailWord_3864355) baseStart_3864355 baseEnd_3864355 := by
    simpa [prefixWord, tailWord_3864355, baseEnd_3864355] using wordTrace_append hprefix tailTrace_3864355
  have hstable : (prefixWord ++ tailWord_3864355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864355).length < 2 ^ (prefixWord ++ tailWord_3864355).sum := by decide
  have hdescent : baseEnd_3864355 < baseStart_3864355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864357 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 5]
def baseStart_3864357 : Nat := 118140960795 + 3864357 * 2 ^ 59
def prefixEnd_3864357 : Nat := 4983230072969 + 3 ^ 40 * 3864357 * 2
def baseEnd_3864357 : Nat := 440949458125920537592367

theorem tailTrace_3864357 : CollatzResearch.WordTrace tailWord_3864357 prefixEnd_3864357 440949458125920537592367 := by
  unfold tailWord_3864357
  simp only [CollatzResearch.WordTrace]
  refine ⟨140944678861102043477047325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93963119240734695651364883 140944678861102043477047325)
  ·
    refine ⟨52854254572913266303892747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140944678861102043477047325 52854254572913266303892747)
    ·
      refine ⟨79281381859369899455839121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52854254572913266303892747 79281381859369899455839121)
      ·
        refine ⟨59461036394527424591879341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79281381859369899455839121 59461036394527424591879341)
        ·
          refine ⟨22297888647947784221954753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59461036394527424591879341 22297888647947784221954753)
          ·
            refine ⟨16723416485960838166466065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22297888647947784221954753 16723416485960838166466065)
            ·
              refine ⟨12542562364470628624849549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16723416485960838166466065 12542562364470628624849549)
              ·
                refine ⟨4703460886676485734318581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12542562364470628624849549 4703460886676485734318581)
                ·
                  refine ⟨440949458125920537592367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4703460886676485734318581 440949458125920537592367)
                  ·
                    rfl

theorem cell22_3864357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_3864357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864357 prefixEnd_3864357 := by exact prefixLift 3864357
  have htrace : WordTrace (prefixWord ++ tailWord_3864357) baseStart_3864357 baseEnd_3864357 := by
    simpa [prefixWord, tailWord_3864357, baseEnd_3864357] using wordTrace_append hprefix tailTrace_3864357
  have hstable : (prefixWord ++ tailWord_3864357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864357).length < 2 ^ (prefixWord ++ tailWord_3864357).sum := by decide
  have hdescent : baseEnd_3864357 < baseStart_3864357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864402 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3864402 : Nat := 118140960795 + 3864402 * 2 ^ 59
def prefixEnd_3864402 : Nat := 4983230072969 + 3 ^ 40 * 3864402 * 2
def baseEnd_3864402 : Nat := 440954592932465498467321

theorem tailTrace_3864402 : CollatzResearch.WordTrace tailWord_3864402 prefixEnd_3864402 440954592932465498467321 := by
  unfold tailWord_3864402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35236580036484754040608865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93964213430626010774956973 35236580036484754040608865)
  ·
    refine ⟨26427435027363565530456649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35236580036484754040608865 26427435027363565530456649)
    ·
      refine ⟨19820576270522674147842487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26427435027363565530456649 19820576270522674147842487)
      ·
        refine ⟨29730864405784011221763731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19820576270522674147842487 29730864405784011221763731)
        ·
          refine ⟨44596296608676016832645597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29730864405784011221763731 44596296608676016832645597)
          ·
            refine ⟨16723611228253506312242099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44596296608676016832645597 16723611228253506312242099)
            ·
              refine ⟨25085416842380259468363149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16723611228253506312242099 25085416842380259468363149)
              ·
                refine ⟨9407031315892597300636181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25085416842380259468363149 9407031315892597300636181)
                ·
                  refine ⟨440954592932465498467321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9407031315892597300636181 440954592932465498467321)
                  ·
                    rfl

theorem cell22_3864402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3864402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864402 prefixEnd_3864402 := by exact prefixLift 3864402
  have htrace : WordTrace (prefixWord ++ tailWord_3864402) baseStart_3864402 baseEnd_3864402 := by
    simpa [prefixWord, tailWord_3864402, baseEnd_3864402] using wordTrace_append hprefix tailTrace_3864402
  have hstable : (prefixWord ++ tailWord_3864402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864402).length < 2 ^ (prefixWord ++ tailWord_3864402).sum := by decide
  have hdescent : baseEnd_3864402 < baseStart_3864402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864432 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_3864432 : Nat := 118140960795 + 3864432 * 2 ^ 59
def prefixEnd_3864432 : Nat := 4983230072969 + 3 ^ 40 * 3864432 * 2
def baseEnd_3864432 : Nat := 1322874048410486417151871

theorem tailTrace_3864432 : CollatzResearch.WordTrace tailWord_3864432 prefixEnd_3864432 1322874048410486417151871 := by
  unfold tailWord_3864432
  simp only [CollatzResearch.WordTrace]
  refine ⟨70473707167915165643013775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93964942890553554190685033 70473707167915165643013775)
  ·
    refine ⟨105710560751872748464520663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70473707167915165643013775 105710560751872748464520663)
    ·
      refine ⟨158565841127809122696780995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105710560751872748464520663 158565841127809122696780995)
      ·
        refine ⟨237848761691713684045171493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158565841127809122696780995 237848761691713684045171493)
        ·
          refine ⟨44596642817196315758469655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237848761691713684045171493 44596642817196315758469655)
          ·
            refine ⟨66894964225794473637704483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44596642817196315758469655 66894964225794473637704483)
            ·
              refine ⟨100342446338691710456556725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66894964225794473637704483 100342446338691710456556725)
              ·
                refine ⟨9407104344252347855302193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100342446338691710456556725 9407104344252347855302193)
                ·
                  refine ⟨7055328258189260891476645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9407104344252347855302193 7055328258189260891476645)
                  ·
                    refine ⟨1322874048410486417151871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7055328258189260891476645 1322874048410486417151871)
                    ·
                      rfl

theorem cell22_3864432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_3864432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864432 prefixEnd_3864432 := by exact prefixLift 3864432
  have htrace : WordTrace (prefixWord ++ tailWord_3864432) baseStart_3864432 baseEnd_3864432 := by
    simpa [prefixWord, tailWord_3864432, baseEnd_3864432] using wordTrace_append hprefix tailTrace_3864432
  have hstable : (prefixWord ++ tailWord_3864432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864432).length < 2 ^ (prefixWord ++ tailWord_3864432).sum := by decide
  have hdescent : baseEnd_3864432 < baseStart_3864432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864468 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3864468 : Nat := 118140960795 + 3864468 * 2 ^ 59
def prefixEnd_3864468 : Nat := 4983230072969 + 3 ^ 40 * 3864468 * 2
def baseEnd_3864468 : Nat := 1322886371946194323251761

theorem tailTrace_3864468 : CollatzResearch.WordTrace tailWord_3864468 prefixEnd_3864468 1322886371946194323251761 := by
  unfold tailWord_3864468
  simp only [CollatzResearch.WordTrace]
  refine ⟨70474363681849954717169029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93965818242466606289558705 70474363681849954717169029)
  ·
    refine ⟨13213943190346866509469193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70474363681849954717169029 13213943190346866509469193)
    ·
      refine ⟨9910457392760149882101895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13213943190346866509469193 9910457392760149882101895)
      ·
        refine ⟨14865686089140224823152843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9910457392760149882101895 14865686089140224823152843)
        ·
          refine ⟨22298529133710337234729265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14865686089140224823152843 22298529133710337234729265)
          ·
            refine ⟨16723896850282752926046949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22298529133710337234729265 16723896850282752926046949)
            ·
              refine ⟨3135730659428016173633803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16723896850282752926046949 3135730659428016173633803)
              ·
                refine ⟨4703595989142024260450705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135730659428016173633803 4703595989142024260450705)
                ·
                  refine ⟨3527696991856518195338029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703595989142024260450705 3527696991856518195338029)
                  ·
                    refine ⟨1322886371946194323251761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527696991856518195338029 1322886371946194323251761)
                    ·
                      rfl

theorem cell22_3864468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3864468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864468 prefixEnd_3864468 := by exact prefixLift 3864468
  have htrace : WordTrace (prefixWord ++ tailWord_3864468) baseStart_3864468 baseEnd_3864468 := by
    simpa [prefixWord, tailWord_3864468, baseEnd_3864468] using wordTrace_append hprefix tailTrace_3864468
  have hstable : (prefixWord ++ tailWord_3864468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864468).length < 2 ^ (prefixWord ++ tailWord_3864468).sum := by decide
  have hdescent : baseEnd_3864468 < baseStart_3864468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864509 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 5]
def baseStart_3864509 : Nat := 118140960795 + 3864509 * 2 ^ 59
def prefixEnd_3864509 : Nat := 4983230072969 + 3 ^ 40 * 3864509 * 2
def baseEnd_3864509 : Nat := 440966802361361294325545

theorem tailTrace_3864509 : CollatzResearch.WordTrace tailWord_3864509 prefixEnd_3864509 440966802361361294325545 := by
  unfold tailWord_3864509
  simp only [CollatzResearch.WordTrace]
  refine ⟨140950222756551373436580581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93966815171034248957720387 140950222756551373436580581)
  ·
    refine ⟨26428166766853382519358859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140950222756551373436580581 26428166766853382519358859)
    ·
      refine ⟨39642250150280073779038289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26428166766853382519358859 39642250150280073779038289)
      ·
        refine ⟨29731687612710055334278717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39642250150280073779038289 29731687612710055334278717)
        ·
          refine ⟨11149382854766270750354519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29731687612710055334278717 11149382854766270750354519)
          ·
            refine ⟨16724074282149406125531779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149382854766270750354519 16724074282149406125531779)
            ·
              refine ⟨25086111423224109188297669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16724074282149406125531779 25086111423224109188297669)
              ·
                refine ⟨4703645891854520472805813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25086111423224109188297669 4703645891854520472805813)
                ·
                  refine ⟨440966802361361294325545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4703645891854520472805813 440966802361361294325545)
                  ·
                    rfl

theorem cell22_3864509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_3864509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864509 prefixEnd_3864509 := by exact prefixLift 3864509
  have htrace : WordTrace (prefixWord ++ tailWord_3864509) baseStart_3864509 baseEnd_3864509 := by
    simpa [prefixWord, tailWord_3864509, baseEnd_3864509] using wordTrace_append hprefix tailTrace_3864509
  have hstable : (prefixWord ++ tailWord_3864509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864509).length < 2 ^ (prefixWord ++ tailWord_3864509).sum := by decide
  have hdescent : baseEnd_3864509 < baseStart_3864509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864524 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_3864524 : Nat := 118140960795 + 3864524 * 2 ^ 59
def prefixEnd_3864524 : Nat := 4983230072969 + 3 ^ 40 * 3864524 * 2
def baseEnd_3864524 : Nat := 1322905541890628843851589

theorem tailTrace_3864524 : CollatzResearch.WordTrace tailWord_3864524 prefixEnd_3864524 1322905541890628843851589 := by
  unfold tailWord_3864524
  simp only [CollatzResearch.WordTrace]
  refine ⟨70475384925748515499188313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93967179900998020665584417 70475384925748515499188313)
  ·
    refine ⟨52856538694311386624391235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70475384925748515499188313 52856538694311386624391235)
    ·
      refine ⟨79284808041467079936586853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52856538694311386624391235 79284808041467079936586853)
      ·
        refine ⟨14865901507775077488110035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79284808041467079936586853 14865901507775077488110035)
        ·
          refine ⟨22298852261662616232165053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14865901507775077488110035 22298852261662616232165053)
          ·
            refine ⟨8362069598123481087061895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22298852261662616232165053 8362069598123481087061895)
            ·
              refine ⟨12543104397185221630592843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362069598123481087061895 12543104397185221630592843)
              ·
                refine ⟨18814656595777832445889265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12543104397185221630592843 18814656595777832445889265)
                ·
                  refine ⟨14110992446833374334416949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18814656595777832445889265 14110992446833374334416949)
                  ·
                    refine ⟨1322905541890628843851589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14110992446833374334416949 1322905541890628843851589)
                    ·
                      rfl

theorem cell22_3864524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_3864524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864524 prefixEnd_3864524 := by exact prefixLift 3864524
  have htrace : WordTrace (prefixWord ++ tailWord_3864524) baseStart_3864524 baseEnd_3864524 := by
    simpa [prefixWord, tailWord_3864524, baseEnd_3864524] using wordTrace_append hprefix tailTrace_3864524
  have hstable : (prefixWord ++ tailWord_3864524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864524).length < 2 ^ (prefixWord ++ tailWord_3864524).sum := by decide
  have hdescent : baseEnd_3864524 < baseStart_3864524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864631 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 3, 3]
def baseStart_3864631 : Nat := 118140960795 + 3864631 * 2 ^ 59
def prefixEnd_3864631 : Nat := 4983230072969 + 3 ^ 40 * 3864631 * 2
def baseEnd_3864631 : Nat := 1322942170177316231426261

theorem tailTrace_3864631 : CollatzResearch.WordTrace tailWord_3864631 prefixEnd_3864631 1322942170177316231426261 := by
  unfold tailWord_3864631
  simp only [CollatzResearch.WordTrace]
  refine ⟨140954672462109388272521747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93969781641406258848347831 140954672462109388272521747)
  ·
    refine ⟨211432008693164082408782621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140954672462109388272521747 211432008693164082408782621)
    ·
      refine ⟨79287003259936530903293483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211432008693164082408782621 79287003259936530903293483)
      ·
        refine ⟨118930504889904796354940225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79287003259936530903293483 118930504889904796354940225)
        ·
          refine ⟨89197878667428597266205169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118930504889904796354940225 89197878667428597266205169)
          ·
            refine ⟨66898409000571447949653877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89197878667428597266205169 66898409000571447949653877)
            ·
              refine ⟨6271725843803573245280051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66898409000571447949653877 6271725843803573245280051)
              ·
                refine ⟨9407588765705359867920077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271725843803573245280051 9407588765705359867920077)
                ·
                  refine ⟨3527845787139509950470029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9407588765705359867920077 3527845787139509950470029)
                  ·
                    refine ⟨1322942170177316231426261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527845787139509950470029 1322942170177316231426261)
                    ·
                      rfl

theorem cell22_3864631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_3864631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864631 prefixEnd_3864631 := by exact prefixLift 3864631
  have htrace : WordTrace (prefixWord ++ tailWord_3864631) baseStart_3864631 baseEnd_3864631 := by
    simpa [prefixWord, tailWord_3864631, baseEnd_3864631] using wordTrace_append hprefix tailTrace_3864631
  have hstable : (prefixWord ++ tailWord_3864631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864631).length < 2 ^ (prefixWord ++ tailWord_3864631).sum := by decide
  have hdescent : baseEnd_3864631 < baseStart_3864631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864689 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 6]
def baseStart_3864689 : Nat := 118140960795 + 3864689 * 2 ^ 59
def prefixEnd_3864689 : Nat := 4983230072969 + 3 ^ 40 * 3864689 * 2
def baseEnd_3864689 : Nat := 440987341587541137825361

theorem tailTrace_3864689 : CollatzResearch.WordTrace tailWord_3864689 prefixEnd_3864689 440987341587541137825361 := by
  unfold tailWord_3864689
  simp only [CollatzResearch.WordTrace]
  refine ⟨140956787895899264178133121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93971191930599509452088747 140956787895899264178133121)
  ·
    refine ⟨105717590921924448133599841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140956787895899264178133121 105717590921924448133599841)
    ·
      refine ⟨79288193191443336100199881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105717590921924448133599841 79288193191443336100199881)
      ·
        refine ⟨59466144893582502075149911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79288193191443336100199881 59466144893582502075149911)
        ·
          refine ⟨89199217340373753112724867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59466144893582502075149911 89199217340373753112724867)
          ·
            refine ⟨133798826010560629669087301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89199217340373753112724867 133798826010560629669087301)
            ·
              refine ⟨25087279876980118062953869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133798826010560629669087301 25087279876980118062953869)
              ·
                refine ⟨9407729953867544273607701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25087279876980118062953869 9407729953867544273607701)
                ·
                  refine ⟨440987341587541137825361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9407729953867544273607701 440987341587541137825361)
                  ·
                    rfl

theorem cell22_3864689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_3864689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864689 prefixEnd_3864689 := by exact prefixLift 3864689
  have htrace : WordTrace (prefixWord ++ tailWord_3864689) baseStart_3864689 baseEnd_3864689 := by
    simpa [prefixWord, tailWord_3864689, baseEnd_3864689] using wordTrace_append hprefix tailTrace_3864689
  have hstable : (prefixWord ++ tailWord_3864689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864689).length < 2 ^ (prefixWord ++ tailWord_3864689).sum := by decide
  have hdescent : baseEnd_3864689 < baseStart_3864689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864768 : List Nat := [2, 1, 1, 2, 5, 3, 2, 6]
def baseStart_3864768 : Nat := 118140960795 + 3864768 * 2 ^ 59
def prefixEnd_3864768 : Nat := 4983230072969 + 3 ^ 40 * 3864768 * 2
def baseEnd_3864768 : Nat := 146998785341899282305649

theorem tailTrace_3864768 : CollatzResearch.WordTrace tailWord_3864768 prefixEnd_3864768 146998785341899282305649 := by
  unfold tailWord_3864768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70479834631306530335129479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93973112841742040446839305 70479834631306530335129479)
  ·
    refine ⟨105719751946959795502694219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70479834631306530335129479 105719751946959795502694219)
    ·
      refine ⟨158579627920439693254041329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105719751946959795502694219 158579627920439693254041329)
      ·
        refine ⟨118934720940329769940530997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158579627920439693254041329 118934720940329769940530997)
        ·
          refine ⟨11150130088155915931924781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118934720940329769940530997 11150130088155915931924781)
          ·
            refine ⟨4181298783058468474471793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11150130088155915931924781 4181298783058468474471793)
            ·
              refine ⟨3135974087293851355853845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4181298783058468474471793 3135974087293851355853845)
              ·
                refine ⟨146998785341899282305649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3135974087293851355853845 146998785341899282305649)
                ·
                  rfl

theorem cell22_3864768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_3864768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864768 prefixEnd_3864768 := by exact prefixLift 3864768
  have htrace : WordTrace (prefixWord ++ tailWord_3864768) baseStart_3864768 baseEnd_3864768 := by
    simpa [prefixWord, tailWord_3864768, baseEnd_3864768] using wordTrace_append hprefix tailTrace_3864768
  have hstable : (prefixWord ++ tailWord_3864768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864768).length < 2 ^ (prefixWord ++ tailWord_3864768).sum := by decide
  have hdescent : baseEnd_3864768 < baseStart_3864768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864770 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3864770 : Nat := 118140960795 + 3864770 * 2 ^ 59
def prefixEnd_3864770 : Nat := 4983230072969 + 3 ^ 40 * 3864770 * 2
def baseEnd_3864770 : Nat := 1322989752717966202200835

theorem tailTrace_3864770 : CollatzResearch.WordTrace tailWord_3864770 prefixEnd_3864770 1322989752717966202200835 := by
  unfold tailWord_3864770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35239935552151453752957941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93973161472403876674554509 35239935552151453752957941)
  ·
    refine ⟨3303743958014198789339807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35239935552151453752957941 3303743958014198789339807)
    ·
      refine ⟨4955615937021298184009711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303743958014198789339807 4955615937021298184009711)
      ·
        refine ⟨7433423905531947276014567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955615937021298184009711 7433423905531947276014567)
        ·
          refine ⟨11150135858297920914021851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7433423905531947276014567 11150135858297920914021851)
          ·
            refine ⟨16725203787446881371032777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11150135858297920914021851 16725203787446881371032777)
            ·
              refine ⟨12543902840585161028274583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16725203787446881371032777 12543902840585161028274583)
              ·
                refine ⟨18815854260877741542411875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12543902840585161028274583 18815854260877741542411875)
                ·
                  refine ⟨28223781391316612313617813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18815854260877741542411875 28223781391316612313617813)
                  ·
                    refine ⟨1322989752717966202200835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28223781391316612313617813 1322989752717966202200835)
                    ·
                      rfl

theorem cell22_3864770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3864770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864770 prefixEnd_3864770 := by exact prefixLift 3864770
  have htrace : WordTrace (prefixWord ++ tailWord_3864770) baseStart_3864770 baseEnd_3864770 := by
    simpa [prefixWord, tailWord_3864770, baseEnd_3864770] using wordTrace_append hprefix tailTrace_3864770
  have hstable : (prefixWord ++ tailWord_3864770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864770).length < 2 ^ (prefixWord ++ tailWord_3864770).sum := by decide
  have hdescent : baseEnd_3864770 < baseStart_3864770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864779 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 9]
def baseStart_3864779 : Nat := 118140960795 + 3864779 * 2 ^ 59
def prefixEnd_3864779 : Nat := 4983230072969 + 3 ^ 40 * 3864779 * 2
def baseEnd_3864779 : Nat := 440997611200631059575269

theorem tailTrace_3864779 : CollatzResearch.WordTrace tailWord_3864779 prefixEnd_3864779 440997611200631059575269 := by
  unfold tailWord_3864779
  simp only [CollatzResearch.WordTrace]
  refine ⟨140960070465573209548909391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93973380310382139699272927 140960070465573209548909391)
  ·
    refine ⟨211440105698359814323364087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140960070465573209548909391 211440105698359814323364087)
    ·
      refine ⟨317160158547539721485046131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211440105698359814323364087 317160158547539721485046131)
      ·
        refine ⟨475740237821309582227569197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317160158547539721485046131 475740237821309582227569197)
        ·
          refine ⟨178402589182991093335338449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475740237821309582227569197 178402589182991093335338449)
          ·
            refine ⟨133801941887243320001503837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178402589182991093335338449 133801941887243320001503837)
            ·
              refine ⟨50175728207716245000563939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133801941887243320001503837 50175728207716245000563939)
              ·
                refine ⟨75263592311574367500845909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50175728207716245000563939 75263592311574367500845909)
                ·
                  refine ⟨440997611200631059575269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75263592311574367500845909 440997611200631059575269)
                  ·
                    rfl

theorem cell22_3864779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_3864779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864779 prefixEnd_3864779 := by exact prefixLift 3864779
  have htrace : WordTrace (prefixWord ++ tailWord_3864779) baseStart_3864779 baseEnd_3864779 := by
    simpa [prefixWord, tailWord_3864779, baseEnd_3864779] using wordTrace_append hprefix tailTrace_3864779
  have hstable : (prefixWord ++ tailWord_3864779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864779).length < 2 ^ (prefixWord ++ tailWord_3864779).sum := by decide
  have hdescent : baseEnd_3864779 < baseStart_3864779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864802 : List Nat := [3, 3, 4, 1, 1, 1, 2, 7]
def baseStart_3864802 : Nat := 118140960795 + 3864802 * 2 ^ 59
def prefixEnd_3864802 : Nat := 4983230072969 + 3 ^ 40 * 3864802 * 2
def baseEnd_3864802 : Nat := 147000078552436531711193

theorem tailTrace_3864802 : CollatzResearch.WordTrace tailWord_3864802 prefixEnd_3864802 147000078552436531711193 := by
  unfold tailWord_3864802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35240227336122471119249165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93973939562993256317997773 35240227336122471119249165)
  ·
    refine ⟨13215085251045926669718437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35240227336122471119249165 13215085251045926669718437)
    ·
      refine ⟨2477828484571111250572207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13215085251045926669718437 2477828484571111250572207)
      ·
        refine ⟨3716742726856666875858311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2477828484571111250572207 3716742726856666875858311)
        ·
          refine ⟨5575114090285000313787467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716742726856666875858311 5575114090285000313787467)
          ·
            refine ⟨8362671135427500470681201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575114090285000313787467 8362671135427500470681201)
            ·
              refine ⟨6272003351570625353010901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8362671135427500470681201 6272003351570625353010901)
              ·
                refine ⟨147000078552436531711193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6272003351570625353010901 147000078552436531711193)
                ·
                  rfl

theorem cell22_3864802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_3864802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864802 prefixEnd_3864802 := by exact prefixLift 3864802
  have htrace : WordTrace (prefixWord ++ tailWord_3864802) baseStart_3864802 baseEnd_3864802 := by
    simpa [prefixWord, tailWord_3864802, baseEnd_3864802] using wordTrace_append hprefix tailTrace_3864802
  have hstable : (prefixWord ++ tailWord_3864802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864802).length < 2 ^ (prefixWord ++ tailWord_3864802).sum := by decide
  have hdescent : baseEnd_3864802 < baseStart_3864802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864856 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_3864856 : Nat := 118140960795 + 3864856 * 2 ^ 59
def prefixEnd_3864856 : Nat := 4983230072969 + 3 ^ 40 * 3864856 * 2
def baseEnd_3864856 : Nat := 1323019192275490644550571

theorem tailTrace_3864856 : CollatzResearch.WordTrace tailWord_3864856 prefixEnd_3864856 1323019192275490644550571 := by
  unfold tailWord_3864856
  simp only [CollatzResearch.WordTrace]
  refine ⟨70481439443147125849731211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93975252590862834466308281 70481439443147125849731211)
  ·
    refine ⟨105722159164720688774596817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70481439443147125849731211 105722159164720688774596817)
    ·
      refine ⟨79291619373540516580947613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105722159164720688774596817 79291619373540516580947613)
      ·
        refine ⟨29734357265077693717855355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79291619373540516580947613 29734357265077693717855355)
        ·
          refine ⟨44601535897616540576783033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29734357265077693717855355 44601535897616540576783033)
          ·
            refine ⟨33451151923212405432587275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44601535897616540576783033 33451151923212405432587275)
            ·
              refine ⟨50176727884818608148880913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33451151923212405432587275 50176727884818608148880913)
              ·
                refine ⟨37632545913613956111660685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50176727884818608148880913 37632545913613956111660685)
                ·
                  refine ⟨14112204717605233541872757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37632545913613956111660685 14112204717605233541872757)
                  ·
                    refine ⟨1323019192275490644550571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14112204717605233541872757 1323019192275490644550571)
                    ·
                      rfl

theorem cell22_3864856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_3864856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864856 prefixEnd_3864856 := by exact prefixLift 3864856
  have htrace : WordTrace (prefixWord ++ tailWord_3864856) baseStart_3864856 baseEnd_3864856 := by
    simpa [prefixWord, tailWord_3864856, baseEnd_3864856] using wordTrace_append hprefix tailTrace_3864856
  have hstable : (prefixWord ++ tailWord_3864856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864856).length < 2 ^ (prefixWord ++ tailWord_3864856).sum := by decide
  have hdescent : baseEnd_3864856 < baseStart_3864856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864888 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_3864888 : Nat := 118140960795 + 3864888 * 2 ^ 59
def prefixEnd_3864888 : Nat := 4983230072969 + 3 ^ 40 * 3864888 * 2
def baseEnd_3864888 : Nat := 1323030146529453227750473

theorem tailTrace_3864888 : CollatzResearch.WordTrace tailWord_3864888 prefixEnd_3864888 1323030146529453227750473 := by
  unfold tailWord_3864888
  simp only [CollatzResearch.WordTrace]
  refine ⟨70482023011089160582313659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93976030681452214109751545 70482023011089160582313659)
  ·
    refine ⟨105723034516633740873470489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70482023011089160582313659 105723034516633740873470489)
    ·
      refine ⟨79292275887475305655102867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105723034516633740873470489 79292275887475305655102867)
      ·
        refine ⟨118938413831212958482654301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79292275887475305655102867 118938413831212958482654301)
        ·
          refine ⟨44601905186704859430995363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118938413831212958482654301 44601905186704859430995363)
          ·
            refine ⟨66902857780057289146493045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44601905186704859430995363 66902857780057289146493045)
            ·
              refine ⟨6272142916880370857483723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66902857780057289146493045 6272142916880370857483723)
              ·
                refine ⟨9408214375320556286225585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272142916880370857483723 9408214375320556286225585)
                ·
                  refine ⟨7056160781490417214669189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9408214375320556286225585 7056160781490417214669189)
                  ·
                    refine ⟨1323030146529453227750473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056160781490417214669189 1323030146529453227750473)
                    ·
                      rfl

theorem cell22_3864888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_3864888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864888 prefixEnd_3864888 := by exact prefixLift 3864888
  have htrace : WordTrace (prefixWord ++ tailWord_3864888) baseStart_3864888 baseEnd_3864888 := by
    simpa [prefixWord, tailWord_3864888, baseEnd_3864888] using wordTrace_append hprefix tailTrace_3864888
  have hstable : (prefixWord ++ tailWord_3864888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864888).length < 2 ^ (prefixWord ++ tailWord_3864888).sum := by decide
  have hdescent : baseEnd_3864888 < baseStart_3864888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864924 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3864924 : Nat := 118140960795 + 3864924 * 2 ^ 59
def prefixEnd_3864924 : Nat := 4983230072969 + 3 ^ 40 * 3864924 * 2
def baseEnd_3864924 : Nat := 1323042470065161133850363

theorem tailTrace_3864924 : CollatzResearch.WordTrace tailWord_3864924 prefixEnd_3864924 1323042470065161133850363 := by
  unfold tailWord_3864924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70482679525023949656468913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93976906033365266208625217 70482679525023949656468913)
  ·
    refine ⟨52862009643767962242351685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70482679525023949656468913 52862009643767962242351685)
    ·
      refine ⟨9911626808206492920440941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52862009643767962242351685 9911626808206492920440941)
      ·
        refine ⟨3716860053077434845165353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9911626808206492920440941 3716860053077434845165353)
        ·
          refine ⟨2787645039808076133874015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716860053077434845165353 2787645039808076133874015)
          ·
            refine ⟨4181467559712114200811023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787645039808076133874015 4181467559712114200811023)
            ·
              refine ⟨6272201339568171301216535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181467559712114200811023 6272201339568171301216535)
              ·
                refine ⟨9408302009352256951824803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272201339568171301216535 9408302009352256951824803)
                ·
                  refine ⟨14112453014028385427737205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9408302009352256951824803 14112453014028385427737205)
                  ·
                    refine ⟨1323042470065161133850363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14112453014028385427737205 1323042470065161133850363)
                    ·
                      rfl

theorem cell22_3864924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3864924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864924 prefixEnd_3864924 := by exact prefixLift 3864924
  have htrace : WordTrace (prefixWord ++ tailWord_3864924) baseStart_3864924 baseEnd_3864924 := by
    simpa [prefixWord, tailWord_3864924, baseEnd_3864924] using wordTrace_append hprefix tailTrace_3864924
  have hstable : (prefixWord ++ tailWord_3864924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864924).length < 2 ^ (prefixWord ++ tailWord_3864924).sum := by decide
  have hdescent : baseEnd_3864924 < baseStart_3864924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864935 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3864935 : Nat := 118140960795 + 3864935 * 2 ^ 59
def prefixEnd_3864935 : Nat := 4983230072969 + 3 ^ 40 * 3864935 * 2
def baseEnd_3864935 : Nat := 1323046235589960771825329

theorem tailTrace_3864935 : CollatzResearch.WordTrace tailWord_3864935 prefixEnd_3864935 1323046235589960771825329 := by
  unfold tailWord_3864935
  simp only [CollatzResearch.WordTrace]
  refine ⟨140965760253008048191588259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93977173502005365461058839 140965760253008048191588259)
  ·
    refine ⟨211448640379512072287382389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140965760253008048191588259 211448640379512072287382389)
    ·
      refine ⟨19823310035579256776942099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211448640379512072287382389 19823310035579256776942099)
      ·
        refine ⟨29734965053368885165413149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19823310035579256776942099 29734965053368885165413149)
        ·
          refine ⟨11150611895013331937029931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29734965053368885165413149 11150611895013331937029931)
          ·
            refine ⟨16725917842519997905544897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11150611895013331937029931 16725917842519997905544897)
            ·
              refine ⟨12544438381889998429158673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16725917842519997905544897 12544438381889998429158673)
              ·
                refine ⟨9408328786417498821869005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12544438381889998429158673 9408328786417498821869005)
                ·
                  refine ⟨3528123294906562058200877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9408328786417498821869005 3528123294906562058200877)
                  ·
                    refine ⟨1323046235589960771825329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3528123294906562058200877 1323046235589960771825329)
                    ·
                      rfl

theorem cell22_3864935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3864935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864935 prefixEnd_3864935 := by exact prefixLift 3864935
  have htrace : WordTrace (prefixWord ++ tailWord_3864935) baseStart_3864935 baseEnd_3864935 := by
    simpa [prefixWord, tailWord_3864935, baseEnd_3864935] using wordTrace_append hprefix tailTrace_3864935
  have hstable : (prefixWord ++ tailWord_3864935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864935).length < 2 ^ (prefixWord ++ tailWord_3864935).sum := by decide
  have hdescent : baseEnd_3864935 < baseStart_3864935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864969 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 1, 3]
def baseStart_3864969 : Nat := 118140960795 + 3864969 * 2 ^ 59
def prefixEnd_3864969 : Nat := 4983230072969 + 3 ^ 40 * 3864969 * 2
def baseEnd_3864969 : Nat := 1323057874484796016475225

theorem tailTrace_3864969 : CollatzResearch.WordTrace tailWord_3864969 prefixEnd_3864969 1323057874484796016475225 := by
  unfold tailWord_3864969
  simp only [CollatzResearch.WordTrace]
  refine ⟨140967000334884871998325961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93978000223256581332217307 140967000334884871998325961)
  ·
    refine ⟨105725250251163653998744471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140967000334884871998325961 105725250251163653998744471)
    ·
      refine ⟨158587875376745480998116707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105725250251163653998744471 158587875376745480998116707)
      ·
        refine ⟨237881813065118221497175061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158587875376745480998116707 237881813065118221497175061)
        ·
          refine ⟨11150709987427416632680081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237881813065118221497175061 11150709987427416632680081)
          ·
            refine ⟨8363032490570562474510061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11150709987427416632680081 8363032490570562474510061)
            ·
              refine ⟨3136137183963960927941273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8363032490570562474510061 3136137183963960927941273)
              ·
                refine ⟨2352102887972970695955955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3136137183963960927941273 2352102887972970695955955)
                ·
                  refine ⟨3528154331959456043933933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352102887972970695955955 3528154331959456043933933)
                  ·
                    refine ⟨1323057874484796016475225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3528154331959456043933933 1323057874484796016475225)
                    ·
                      rfl

theorem cell22_3864969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_3864969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864969 prefixEnd_3864969 := by exact prefixLift 3864969
  have htrace : WordTrace (prefixWord ++ tailWord_3864969) baseStart_3864969 baseEnd_3864969 := by
    simpa [prefixWord, tailWord_3864969, baseEnd_3864969] using wordTrace_append hprefix tailTrace_3864969
  have hstable : (prefixWord ++ tailWord_3864969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864969).length < 2 ^ (prefixWord ++ tailWord_3864969).sum := by decide
  have hdescent : baseEnd_3864969 < baseStart_3864969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864976 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_3864976 : Nat := 118140960795 + 3864976 * 2 ^ 59
def prefixEnd_3864976 : Nat := 4983230072969 + 3 ^ 40 * 3864976 * 2
def baseEnd_3864976 : Nat := 441020090242616777183401

theorem tailTrace_3864976 : CollatzResearch.WordTrace tailWord_3864976 prefixEnd_3864976 441020090242616777183401 := by
  unfold tailWord_3864976
  simp only [CollatzResearch.WordTrace]
  refine ⟨70483627822929756096915391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93978170430573008129220521 70483627822929756096915391)
  ·
    refine ⟨105725441734394634145373087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70483627822929756096915391 105725441734394634145373087)
    ·
      refine ⟨158588162601591951218059631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105725441734394634145373087 158588162601591951218059631)
      ·
        refine ⟨237882243902387926827089447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158588162601591951218059631 237882243902387926827089447)
        ·
          refine ⟨356823365853581890240634171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237882243902387926827089447 356823365853581890240634171)
          ·
            refine ⟨535235048780372835360951257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356823365853581890240634171 535235048780372835360951257)
            ·
              refine ⟨401426286585279626520713443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535235048780372835360951257 401426286585279626520713443)
              ·
                refine ⟨602139429877919439781070165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401426286585279626520713443 602139429877919439781070165)
                ·
                  refine ⟨441020090242616777183401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 602139429877919439781070165 441020090242616777183401)
                  ·
                    rfl

theorem cell22_3864976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_3864976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864976 prefixEnd_3864976 := by exact prefixLift 3864976
  have htrace : WordTrace (prefixWord ++ tailWord_3864976) baseStart_3864976 baseEnd_3864976 := by
    simpa [prefixWord, tailWord_3864976, baseEnd_3864976] using wordTrace_append hprefix tailTrace_3864976
  have hstable : (prefixWord ++ tailWord_3864976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864976).length < 2 ^ (prefixWord ++ tailWord_3864976).sum := by decide
  have hdescent : baseEnd_3864976 < baseStart_3864976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864995 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 1, 4]
def baseStart_3864995 : Nat := 118140960795 + 3864995 * 2 ^ 59
def prefixEnd_3864995 : Nat := 4983230072969 + 3 ^ 40 * 3864995 * 2
def baseEnd_3864995 : Nat := 1323066774816140615325145

theorem tailTrace_3864995 : CollatzResearch.WordTrace tailWord_3864995 prefixEnd_3864995 1323066774816140615325145 := by
  unfold tailWord_3864995
  simp only [CollatzResearch.WordTrace]
  refine ⟨140967948632790678438772439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93978632421860452292514959 140967948632790678438772439)
  ·
    refine ⟨211451922949186017658158659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140967948632790678438772439 211451922949186017658158659)
    ·
      refine ⟨317177884423779026487237989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211451922949186017658158659 317177884423779026487237989)
      ·
        refine ⟨59470853329458567466357123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317177884423779026487237989 59470853329458567466357123)
        ·
          refine ⟨89206279994187851199535685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59470853329458567466357123 89206279994187851199535685)
          ·
            refine ⟨16726177498910222099912941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89206279994187851199535685 16726177498910222099912941)
            ·
              refine ⟨6272316562091333287467353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16726177498910222099912941 6272316562091333287467353)
              ·
                refine ⟨4704237421568499965600515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272316562091333287467353 4704237421568499965600515)
                ·
                  refine ⟨7056356132352749948400773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704237421568499965600515 7056356132352749948400773)
                  ·
                    refine ⟨1323066774816140615325145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056356132352749948400773 1323066774816140615325145)
                    ·
                      rfl

theorem cell22_3864995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 4].length) (baseStart_3864995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3864995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3864995 prefixEnd_3864995 := by exact prefixLift 3864995
  have htrace : WordTrace (prefixWord ++ tailWord_3864995) baseStart_3864995 baseEnd_3864995 := by
    simpa [prefixWord, tailWord_3864995, baseEnd_3864995] using wordTrace_append hprefix tailTrace_3864995
  have hstable : (prefixWord ++ tailWord_3864995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864995).length < 2 ^ (prefixWord ++ tailWord_3864995).sum := by decide
  have hdescent : baseEnd_3864995 < baseStart_3864995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865010 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_3865010 : Nat := 118140960795 + 3865010 * 2 ^ 59
def prefixEnd_3865010 : Nat := 4983230072969 + 3 ^ 40 * 3865010 * 2
def baseEnd_3865010 : Nat := 441023969874228525400033

theorem tailTrace_3865010 : CollatzResearch.WordTrace tailWord_3865010 prefixEnd_3865010 441023969874228525400033 := by
  unfold tailWord_3865010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35242123931934084000142121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93978997151824224000378989 35242123931934084000142121)
  ·
    refine ⟨26431592948950563000106591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35242123931934084000142121 26431592948950563000106591)
    ·
      refine ⟨39647389423425844500159887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26431592948950563000106591 39647389423425844500159887)
      ·
        refine ⟨59471084135138766750239831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39647389423425844500159887 59471084135138766750239831)
        ·
          refine ⟨89206626202708150125359747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59471084135138766750239831 89206626202708150125359747)
          ·
            refine ⟨133809939304062225188039621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89206626202708150125359747 133809939304062225188039621)
            ·
              refine ⟨25089363619511667222757429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133809939304062225188039621 25089363619511667222757429)
              ·
                refine ⟨2352127839329218802133509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25089363619511667222757429 2352127839329218802133509)
                ·
                  refine ⟨441023969874228525400033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352127839329218802133509 441023969874228525400033)
                  ·
                    rfl

theorem cell22_3865010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_3865010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865010 prefixEnd_3865010 := by exact prefixLift 3865010
  have htrace : WordTrace (prefixWord ++ tailWord_3865010) baseStart_3865010 baseEnd_3865010 := by
    simpa [prefixWord, tailWord_3865010, baseEnd_3865010] using wordTrace_append hprefix tailTrace_3865010
  have hstable : (prefixWord ++ tailWord_3865010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865010).length < 2 ^ (prefixWord ++ tailWord_3865010).sum := by decide
  have hdescent : baseEnd_3865010 < baseStart_3865010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865055 : List Nat := [1, 1, 2, 3, 3, 3, 3, 6]
def baseStart_3865055 : Nat := 118140960795 + 3865055 * 2 ^ 59
def prefixEnd_3865055 : Nat := 4983230072969 + 3 ^ 40 * 3865055 * 2
def baseEnd_3865055 : Nat := 147009701560257828758329

theorem tailTrace_3865055 : CollatzResearch.WordTrace tailWord_3865055 prefixEnd_3865055 147009701560257828758329 := by
  unfold tailWord_3865055
  simp only [CollatzResearch.WordTrace]
  refine ⟨140970137012573308685956619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93980091341715539123971079 140970137012573308685956619)
  ·
    refine ⟨211455205518859963028934929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140970137012573308685956619 211455205518859963028934929)
    ·
      refine ⟨158591404139144972271701197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211455205518859963028934929 158591404139144972271701197)
      ·
        refine ⟨59471776552179364601887949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158591404139144972271701197 59471776552179364601887949)
        ·
          refine ⟨22301916207067261725707981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59471776552179364601887949 22301916207067261725707981)
          ·
            refine ⟨8363218577650223147140493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22301916207067261725707981 8363218577650223147140493)
            ·
              refine ⟨3136206966618833680177685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8363218577650223147140493 3136206966618833680177685)
              ·
                refine ⟨147009701560257828758329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3136206966618833680177685 147009701560257828758329)
                ·
                  rfl

theorem cell22_3865055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 6].length) (baseStart_3865055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865055 prefixEnd_3865055 := by exact prefixLift 3865055
  have htrace : WordTrace (prefixWord ++ tailWord_3865055) baseStart_3865055 baseEnd_3865055 := by
    simpa [prefixWord, tailWord_3865055, baseEnd_3865055] using wordTrace_append hprefix tailTrace_3865055
  have hstable : (prefixWord ++ tailWord_3865055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865055).length < 2 ^ (prefixWord ++ tailWord_3865055).sum := by decide
  have hdescent : baseEnd_3865055 < baseStart_3865055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865087 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 1, 3]
def baseStart_3865087 : Nat := 118140960795 + 3865087 * 2 ^ 59
def prefixEnd_3865087 : Nat := 4983230072969 + 3 ^ 40 * 3865087 * 2
def baseEnd_3865087 : Nat := 1323098268296283042024863

theorem tailTrace_3865087 : CollatzResearch.WordTrace tailWord_3865087 prefixEnd_3865087 1323098268296283042024863 := by
  unfold tailWord_3865087
  simp only [CollatzResearch.WordTrace]
  refine ⟨140971304148457378151121515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93980869432304918767414343 140971304148457378151121515)
  ·
    refine ⟨211456956222686067226682273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140971304148457378151121515 211456956222686067226682273)
    ·
      refine ⟨158592717167014550420011705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211456956222686067226682273 158592717167014550420011705)
      ·
        refine ⟨118944537875260912815008779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158592717167014550420011705 118944537875260912815008779)
        ·
          refine ⟨178416806812891369222513169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118944537875260912815008779 178416806812891369222513169)
          ·
            refine ⟨133812605109668526916884877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178416806812891369222513169 133812605109668526916884877)
            ·
              refine ⟨50179726916125697593831829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133812605109668526916884877 50179726916125697593831829)
              ·
                refine ⟨2352174699193392074710867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50179726916125697593831829 2352174699193392074710867)
                ·
                  refine ⟨3528262048790088112066301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352174699193392074710867 3528262048790088112066301)
                  ·
                    refine ⟨1323098268296283042024863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3528262048790088112066301 1323098268296283042024863)
                    ·
                      rfl

theorem cell22_3865087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_3865087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865087 prefixEnd_3865087 := by exact prefixLift 3865087
  have htrace : WordTrace (prefixWord ++ tailWord_3865087) baseStart_3865087 baseEnd_3865087 := by
    simpa [prefixWord, tailWord_3865087, baseEnd_3865087] using wordTrace_append hprefix tailTrace_3865087
  have hstable : (prefixWord ++ tailWord_3865087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865087).length < 2 ^ (prefixWord ++ tailWord_3865087).sum := by decide
  have hdescent : baseEnd_3865087 < baseStart_3865087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865194 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_3865194 : Nat := 118140960795 + 3865194 * 2 ^ 59
def prefixEnd_3865194 : Nat := 4983230072969 + 3 ^ 40 * 3865194 * 2
def baseEnd_3865194 : Nat := 1323134896582970429599535

theorem tailTrace_3865194 : CollatzResearch.WordTrace tailWord_3865194 prefixEnd_3865194 1323134896582970429599535 := by
  unfold tailWord_3865194
  simp only [CollatzResearch.WordTrace]
  refine ⟨35243801689767433856316659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93983471172713156950177757 35243801689767433856316659)
  ·
    refine ⟨52865702534651150784474989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35243801689767433856316659 52865702534651150784474989)
    ·
      refine ⟨19824638450494181544178121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52865702534651150784474989 19824638450494181544178121)
      ·
        refine ⟨14868478837870636158133591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19824638450494181544178121 14868478837870636158133591)
        ·
          refine ⟨22302718256805954237200387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14868478837870636158133591 22302718256805954237200387)
          ·
            refine ⟨33454077385208931355800581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22302718256805954237200387 33454077385208931355800581)
            ·
              refine ⟨6272639509726674629212609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33454077385208931355800581 6272639509726674629212609)
              ·
                refine ⟨4704479632295005971909457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272639509726674629212609 4704479632295005971909457)
                ·
                  refine ⟨3528359724221254478932093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4704479632295005971909457 3528359724221254478932093)
                  ·
                    refine ⟨1323134896582970429599535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3528359724221254478932093 1323134896582970429599535)
                    ·
                      rfl

theorem cell22_3865194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_3865194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865194 prefixEnd_3865194 := by exact prefixLift 3865194
  have htrace : WordTrace (prefixWord ++ tailWord_3865194) baseStart_3865194 baseEnd_3865194 := by
    simpa [prefixWord, tailWord_3865194, baseEnd_3865194] using wordTrace_append hprefix tailTrace_3865194
  have hstable : (prefixWord ++ tailWord_3865194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865194).length < 2 ^ (prefixWord ++ tailWord_3865194).sum := by decide
  have hdescent : baseEnd_3865194 < baseStart_3865194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865226 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_3865226 : Nat := 118140960795 + 3865226 * 2 ^ 59
def prefixEnd_3865226 : Nat := 4983230072969 + 3 ^ 40 * 3865226 * 2
def baseEnd_3865226 : Nat := 1323145850836933012799437

theorem tailTrace_3865226 : CollatzResearch.WordTrace tailWord_3865226 prefixEnd_3865226 1323145850836933012799437 := by
  unfold tailWord_3865226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35244093473738451222607883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93984249263302536593621021 35244093473738451222607883)
  ·
    refine ⟨52866140210607676833911825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35244093473738451222607883 52866140210607676833911825)
    ·
      refine ⟨39649605157955757625433869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52866140210607676833911825 39649605157955757625433869)
      ·
        refine ⟨14868601934233409109537701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39649605157955757625433869 14868601934233409109537701)
        ·
          refine ⟨2787862862668764208038319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14868601934233409109537701 2787862862668764208038319)
          ·
            refine ⟨4181794294003146312057479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787862862668764208038319 4181794294003146312057479)
            ·
              refine ⟨6272691441004719468086219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181794294003146312057479 6272691441004719468086219)
              ·
                refine ⟨9409037161507079202129329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272691441004719468086219 9409037161507079202129329)
                ·
                  refine ⟨7056777871130309401596997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9409037161507079202129329 7056777871130309401596997)
                  ·
                    refine ⟨1323145850836933012799437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056777871130309401596997 1323145850836933012799437)
                    ·
                      rfl

theorem cell22_3865226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_3865226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865226 prefixEnd_3865226 := by exact prefixLift 3865226
  have htrace : WordTrace (prefixWord ++ tailWord_3865226) baseStart_3865226 baseEnd_3865226 := by
    simpa [prefixWord, tailWord_3865226, baseEnd_3865226] using wordTrace_append hprefix tailTrace_3865226
  have hstable : (prefixWord ++ tailWord_3865226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865226).length < 2 ^ (prefixWord ++ tailWord_3865226).sum := by decide
  have hdescent : baseEnd_3865226 < baseStart_3865226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865329 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_3865329 : Nat := 118140960795 + 3865329 * 2 ^ 59
def prefixEnd_3865329 : Nat := 4983230072969 + 3 ^ 40 * 3865329 * 2
def baseEnd_3865329 : Nat := 1323181109841875077474121

theorem tailTrace_3865329 : CollatzResearch.WordTrace tailWord_3865329 prefixEnd_3865329 1323181109841875077474121 := by
  unfold tailWord_3865329
  simp only [CollatzResearch.WordTrace]
  refine ⟨140980130613580653481431041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93986753742387102320954027 140980130613580653481431041)
  ·
    refine ⟨105735097960185490111073281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140980130613580653481431041 105735097960185490111073281)
    ·
      refine ⟨79301323470139117583304961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105735097960185490111073281 79301323470139117583304961)
      ·
        refine ⟨59475992602604338187478721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79301323470139117583304961 59475992602604338187478721)
        ·
          refine ⟨44606994451953253640609041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59475992602604338187478721 44606994451953253640609041)
          ·
            refine ⟨33455245838964940230456781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44606994451953253640609041 33455245838964940230456781)
            ·
              refine ⟨12545717189611852586421293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33455245838964940230456781 12545717189611852586421293)
              ·
                refine ⟨4704643946104444719907985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12545717189611852586421293 4704643946104444719907985)
                ·
                  refine ⟨3528482959578333539930989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4704643946104444719907985 3528482959578333539930989)
                  ·
                    refine ⟨1323181109841875077474121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3528482959578333539930989 1323181109841875077474121)
                    ·
                      rfl

theorem cell22_3865329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_3865329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865329 prefixEnd_3865329 := by exact prefixLift 3865329
  have htrace : WordTrace (prefixWord ++ tailWord_3865329) baseStart_3865329 baseEnd_3865329 := by
    simpa [prefixWord, tailWord_3865329, baseEnd_3865329] using wordTrace_append hprefix tailTrace_3865329
  have hstable : (prefixWord ++ tailWord_3865329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865329).length < 2 ^ (prefixWord ++ tailWord_3865329).sum := by decide
  have hdescent : baseEnd_3865329 < baseStart_3865329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865333 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3865333 : Nat := 118140960795 + 3865333 * 2 ^ 59
def prefixEnd_3865333 : Nat := 4983230072969 + 3 ^ 40 * 3865333 * 2
def baseEnd_3865333 : Nat := 1323182479123620400374109

theorem tailTrace_3865333 : CollatzResearch.WordTrace tailWord_3865333 prefixEnd_3865333 1323182479123620400374109 := by
  unfold tailWord_3865333
  simp only [CollatzResearch.WordTrace]
  refine ⟨140980276505566162164576653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93986851003710774776384435 140980276505566162164576653)
  ·
    refine ⟨52867603689587310811716245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140980276505566162164576653 52867603689587310811716245)
    ·
      refine ⟨2478168922949405194299199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52867603689587310811716245 2478168922949405194299199)
      ·
        refine ⟨3717253384424107791448799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478168922949405194299199 3717253384424107791448799)
        ·
          refine ⟨5575880076636161687173199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717253384424107791448799 5575880076636161687173199)
          ·
            refine ⟨8363820114954242530759799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575880076636161687173199 8363820114954242530759799)
            ·
              refine ⟨12545730172431363796139699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363820114954242530759799 12545730172431363796139699)
              ·
                refine ⟨18818595258647045694209549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545730172431363796139699 18818595258647045694209549)
                ·
                  refine ⟨7056973221992642135328581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18818595258647045694209549 7056973221992642135328581)
                  ·
                    refine ⟨1323182479123620400374109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056973221992642135328581 1323182479123620400374109)
                    ·
                      rfl

theorem cell22_3865333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3865333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865333 prefixEnd_3865333 := by exact prefixLift 3865333
  have htrace : WordTrace (prefixWord ++ tailWord_3865333) baseStart_3865333 baseEnd_3865333 := by
    simpa [prefixWord, tailWord_3865333, baseEnd_3865333] using wordTrace_append hprefix tailTrace_3865333
  have hstable : (prefixWord ++ tailWord_3865333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865333).length < 2 ^ (prefixWord ++ tailWord_3865333).sum := by decide
  have hdescent : baseEnd_3865333 < baseStart_3865333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865372 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3865372 : Nat := 118140960795 + 3865372 * 2 ^ 59
def prefixEnd_3865372 : Nat := 4983230072969 + 3 ^ 40 * 3865372 * 2
def baseEnd_3865372 : Nat := 1323195829620637298648989

theorem tailTrace_3865372 : CollatzResearch.WordTrace tailWord_3865372 prefixEnd_3865372 1323195829620637298648989 := by
  unfold tailWord_3865372
  simp only [CollatzResearch.WordTrace]
  refine ⟨70490849476212435912623185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93987799301616581216830913 70490849476212435912623185)
  ·
    refine ⟨52868137107159326934467389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70490849476212435912623185 52868137107159326934467389)
    ·
      refine ⟨19825551415184747600425271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52868137107159326934467389 19825551415184747600425271)
      ·
        refine ⟨29738327122777121400637907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19825551415184747600425271 29738327122777121400637907)
        ·
          refine ⟨44607490684165682100956861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29738327122777121400637907 44607490684165682100956861)
          ·
            refine ⟨16727809006562130787858823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44607490684165682100956861 16727809006562130787858823)
            ·
              refine ⟨25091713509843196181788235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16727809006562130787858823 25091713509843196181788235)
              ·
                refine ⟨37637570264764794272682353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25091713509843196181788235 37637570264764794272682353)
                ·
                  refine ⟨28228177698573595704511765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37637570264764794272682353 28228177698573595704511765)
                  ·
                    refine ⟨1323195829620637298648989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28228177698573595704511765 1323195829620637298648989)
                    ·
                      rfl

theorem cell22_3865372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3865372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865372 prefixEnd_3865372 := by exact prefixLift 3865372
  have htrace : WordTrace (prefixWord ++ tailWord_3865372) baseStart_3865372 baseEnd_3865372 := by
    simpa [prefixWord, tailWord_3865372, baseEnd_3865372] using wordTrace_append hprefix tailTrace_3865372
  have hstable : (prefixWord ++ tailWord_3865372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865372).length < 2 ^ (prefixWord ++ tailWord_3865372).sum := by decide
  have hdescent : baseEnd_3865372 < baseStart_3865372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865421 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3865421 : Nat := 118140960795 + 3865421 * 2 ^ 59
def prefixEnd_3865421 : Nat := 4983230072969 + 3 ^ 40 * 3865421 * 2
def baseEnd_3865421 : Nat := 441070867774005834724613

theorem tailTrace_3865421 : CollatzResearch.WordTrace tailWord_3865421 prefixEnd_3865421 441070867774005834724613 := by
  unfold tailWord_3865421
  simp only [CollatzResearch.WordTrace]
  refine ⟨140983486129247353193780117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93988990752831568795853411 140983486129247353193780117)
  ·
    refine ⟨6608600912308469680958443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140983486129247353193780117 6608600912308469680958443)
    ·
      refine ⟨9912901368462704521437665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6608600912308469680958443 9912901368462704521437665)
      ·
        refine ⟨7434676026347028391078249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9912901368462704521437665 7434676026347028391078249)
        ·
          refine ⟨5576007019760271293308687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7434676026347028391078249 5576007019760271293308687)
          ·
            refine ⟨8364010529640406939963031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576007019760271293308687 8364010529640406939963031)
            ·
              refine ⟨12546015794460610409944547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364010529640406939963031 12546015794460610409944547)
              ·
                refine ⟨18819023691690915614916821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12546015794460610409944547 18819023691690915614916821)
                ·
                  refine ⟨441070867774005834724613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18819023691690915614916821 441070867774005834724613)
                  ·
                    rfl

theorem cell22_3865421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3865421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865421 prefixEnd_3865421 := by exact prefixLift 3865421
  have htrace : WordTrace (prefixWord ++ tailWord_3865421) baseStart_3865421 baseEnd_3865421 := by
    simpa [prefixWord, tailWord_3865421, baseEnd_3865421] using wordTrace_append hprefix tailTrace_3865421
  have hstable : (prefixWord ++ tailWord_3865421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865421).length < 2 ^ (prefixWord ++ tailWord_3865421).sum := by decide
  have hdescent : baseEnd_3865421 < baseStart_3865421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865477 : List Nat := [1, 3, 1, 1, 3, 3, 10]
def baseStart_3865477 : Nat := 118140960795 + 3865477 * 2 ^ 59
def prefixEnd_3865477 : Nat := 4983230072969 + 3 ^ 40 * 3865477 * 2
def baseEnd_3865477 : Nat := 49008584195053778695321

theorem tailTrace_3865477 : CollatzResearch.WordTrace tailWord_3865477 prefixEnd_3865477 49008584195053778695321 := by
  unfold tailWord_3865477
  simp only [CollatzResearch.WordTrace]
  refine ⟨140985528617044474757818685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93990352411362983171879123 140985528617044474757818685)
  ·
    refine ⟨52869573231391678034182007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140985528617044474757818685 52869573231391678034182007)
    ·
      refine ⟨79304359847087517051273011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52869573231391678034182007 79304359847087517051273011)
      ·
        refine ⟨118956539770631275576909517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79304359847087517051273011 118956539770631275576909517)
        ·
          refine ⟨44608702413986728341341069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118956539770631275576909517 44608702413986728341341069)
          ·
            refine ⟨16728263405245023128002901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44608702413986728341341069 16728263405245023128002901)
            ·
              refine ⟨49008584195053778695321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16728263405245023128002901 49008584195053778695321)
              ·
                rfl

theorem cell22_3865477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 10].length) (baseStart_3865477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865477 prefixEnd_3865477 := by exact prefixLift 3865477
  have htrace : WordTrace (prefixWord ++ tailWord_3865477) baseStart_3865477 baseEnd_3865477 := by
    simpa [prefixWord, tailWord_3865477, baseEnd_3865477] using wordTrace_append hprefix tailTrace_3865477
  have hstable : (prefixWord ++ tailWord_3865477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865477).length < 2 ^ (prefixWord ++ tailWord_3865477).sum := by decide
  have hdescent : baseEnd_3865477 < baseStart_3865477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865479 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 4, 4]
def baseStart_3865479 : Nat := 118140960795 + 3865479 * 2 ^ 59
def prefixEnd_3865479 : Nat := 4983230072969 + 3 ^ 40 * 3865479 * 2
def baseEnd_3865479 : Nat := 1323232457907324686223661

theorem tailTrace_3865479 : CollatzResearch.WordTrace tailWord_3865479 prefixEnd_3865479 1323232457907324686223661 := by
  unfold tailWord_3865479
  simp only [CollatzResearch.WordTrace]
  refine ⟨140985601563037229099391491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93990401042024819399594327 140985601563037229099391491)
  ·
    refine ⟨211478402344555843649087237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140985601563037229099391491 211478402344555843649087237)
    ·
      refine ⟨39652200439604220684203857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211478402344555843649087237 39652200439604220684203857)
      ·
        refine ⟨29739150329703165513152893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39652200439604220684203857 29739150329703165513152893)
        ·
          refine ⟨11152181373638687067432335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29739150329703165513152893 11152181373638687067432335)
          ·
            refine ⟨16728272060458030601148503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11152181373638687067432335 16728272060458030601148503)
            ·
              refine ⟨25092408090687045901722755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16728272060458030601148503 25092408090687045901722755)
              ·
                refine ⟨37638612136030568852584133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25092408090687045901722755 37638612136030568852584133)
                ·
                  refine ⟨7057239775505731659859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37638612136030568852584133 7057239775505731659859525)
                  ·
                    refine ⟨1323232457907324686223661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7057239775505731659859525 1323232457907324686223661)
                    ·
                      rfl

theorem cell22_3865479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_3865479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865479 prefixEnd_3865479 := by exact prefixLift 3865479
  have htrace : WordTrace (prefixWord ++ tailWord_3865479) baseStart_3865479 baseEnd_3865479 := by
    simpa [prefixWord, tailWord_3865479, baseEnd_3865479] using wordTrace_append hprefix tailTrace_3865479
  have hstable : (prefixWord ++ tailWord_3865479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865479).length < 2 ^ (prefixWord ++ tailWord_3865479).sum := by decide
  have hdescent : baseEnd_3865479 < baseStart_3865479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865498 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_3865498 : Nat := 118140960795 + 3865498 * 2 ^ 59
def prefixEnd_3865498 : Nat := 4983230072969 + 3 ^ 40 * 3865498 * 2
def baseEnd_3865498 : Nat := 1323238961995614969998603

theorem tailTrace_3865498 : CollatzResearch.WordTrace tailWord_3865498 prefixEnd_3865498 1323238961995614969998603 := by
  unfold tailWord_3865498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35246573637492098836083287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93990863033312263562888765 35246573637492098836083287)
  ·
    refine ⟨52869860456238148254124931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35246573637492098836083287 52869860456238148254124931)
    ·
      refine ⟨79304790684357222381187397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52869860456238148254124931 79304790684357222381187397)
      ·
        refine ⟨14869648253316979196472637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79304790684357222381187397 14869648253316979196472637)
        ·
          refine ⟨5576118094993867198677239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14869648253316979196472637 5576118094993867198677239)
          ·
            refine ⟨8364177142490800798015859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576118094993867198677239 8364177142490800798015859)
            ·
              refine ⟨12546265713736201197023789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364177142490800798015859 12546265713736201197023789)
              ·
                refine ⟨4704849642651075448883921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12546265713736201197023789 4704849642651075448883921)
                ·
                  refine ⟨3528637231988306586662941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4704849642651075448883921 3528637231988306586662941)
                  ·
                    refine ⟨1323238961995614969998603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3528637231988306586662941 1323238961995614969998603)
                    ·
                      rfl

theorem cell22_3865498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_3865498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865498 prefixEnd_3865498 := by exact prefixLift 3865498
  have htrace : WordTrace (prefixWord ++ tailWord_3865498) baseStart_3865498 baseEnd_3865498 := by
    simpa [prefixWord, tailWord_3865498, baseEnd_3865498] using wordTrace_append hprefix tailTrace_3865498
  have hstable : (prefixWord ++ tailWord_3865498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865498).length < 2 ^ (prefixWord ++ tailWord_3865498).sum := by decide
  have hdescent : baseEnd_3865498 < baseStart_3865498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865556 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3865556 : Nat := 118140960795 + 3865556 * 2 ^ 59
def prefixEnd_3865556 : Nat := 4983230072969 + 3 ^ 40 * 3865556 * 2
def baseEnd_3865556 : Nat := 441086272193640717349475

theorem tailTrace_3865556 : CollatzResearch.WordTrace tailWord_3865556 prefixEnd_3865556 441086272193640717349475 := by
  unfold tailWord_3865556
  simp only [CollatzResearch.WordTrace]
  refine ⟨70494204991879135624972261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93992273322505514166629681 70494204991879135624972261)
  ·
    refine ⟨13217663435977337929682299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70494204991879135624972261 13217663435977337929682299)
    ·
      refine ⟨19826495153966006894523449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13217663435977337929682299 19826495153966006894523449)
      ·
        refine ⟨14869871365474505170892587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19826495153966006894523449 14869871365474505170892587)
        ·
          refine ⟨22304807048211757756338881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14869871365474505170892587 22304807048211757756338881)
          ·
            refine ⟨16728605286158818317254161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22304807048211757756338881 16728605286158818317254161)
            ·
              refine ⟨12546453964619113737940621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16728605286158818317254161 12546453964619113737940621)
              ·
                refine ⟨4704920236732167651727733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12546453964619113737940621 4704920236732167651727733)
                ·
                  refine ⟨441086272193640717349475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4704920236732167651727733 441086272193640717349475)
                  ·
                    rfl

theorem cell22_3865556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3865556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865556 prefixEnd_3865556 := by exact prefixLift 3865556
  have htrace : WordTrace (prefixWord ++ tailWord_3865556) baseStart_3865556 baseEnd_3865556 := by
    simpa [prefixWord, tailWord_3865556, baseEnd_3865556] using wordTrace_append hprefix tailTrace_3865556
  have hstable : (prefixWord ++ tailWord_3865556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865556).length < 2 ^ (prefixWord ++ tailWord_3865556).sum := by decide
  have hdescent : baseEnd_3865556 < baseStart_3865556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865601 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 6]
def baseStart_3865601 : Nat := 118140960795 + 3865601 * 2 ^ 59
def prefixEnd_3865601 : Nat := 4983230072969 + 3 ^ 40 * 3865601 * 2
def baseEnd_3865601 : Nat := 441091407000185678224429

theorem tailTrace_3865601 : CollatzResearch.WordTrace tailWord_3865601 prefixEnd_3865601 441091407000185678224429 := by
  unfold tailWord_3865601
  simp only [CollatzResearch.WordTrace]
  refine ⟨140990051268595243935332657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93993367512396829290221771 140990051268595243935332657)
  ·
    refine ⟨105742538451446432951499493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140990051268595243935332657 105742538451446432951499493)
    ·
      refine ⟨19826725959646206178406155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105742538451446432951499493 19826725959646206178406155)
      ·
        refine ⟨29740088939469309267609233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19826725959646206178406155 29740088939469309267609233)
        ·
          refine ⟨22305066704601981950706925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29740088939469309267609233 22305066704601981950706925)
          ·
            refine ⟨8364400014225743231515097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22305066704601981950706925 8364400014225743231515097)
            ·
              refine ⟨6273300010669307423636323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8364400014225743231515097 6273300010669307423636323)
              ·
                refine ⟨9409950016003961135454485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273300010669307423636323 9409950016003961135454485)
                ·
                  refine ⟨441091407000185678224429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9409950016003961135454485 441091407000185678224429)
                  ·
                    rfl

theorem cell22_3865601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_3865601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865601 prefixEnd_3865601 := by exact prefixLift 3865601
  have htrace : WordTrace (prefixWord ++ tailWord_3865601) baseStart_3865601 baseEnd_3865601 := by
    simpa [prefixWord, tailWord_3865601, baseEnd_3865601] using wordTrace_append hprefix tailTrace_3865601
  have hstable : (prefixWord ++ tailWord_3865601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865601).length < 2 ^ (prefixWord ++ tailWord_3865601).sum := by decide
  have hdescent : baseEnd_3865601 < baseStart_3865601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865652 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3865652 : Nat := 118140960795 + 3865652 * 2 ^ 59
def prefixEnd_3865652 : Nat := 4983230072969 + 3 ^ 40 * 3865652 * 2
def baseEnd_3865652 : Nat := 441097226447603300549377

theorem tailTrace_3865652 : CollatzResearch.WordTrace tailWord_3865652 prefixEnd_3865652 441097226447603300549377 := by
  unfold tailWord_3865652
  simp only [CollatzResearch.WordTrace]
  refine ⟨70495955695705239822719605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93994607594273653096959473 70495955695705239822719605)
  ·
    refine ⟨6608995846472366233379963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70495955695705239822719605 6608995846472366233379963)
    ·
      refine ⟨9913493769708549350069945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6608995846472366233379963 9913493769708549350069945)
      ·
        refine ⟨7435120327281412012552459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9913493769708549350069945 7435120327281412012552459)
        ·
          refine ⟨11152680490922118018828689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435120327281412012552459 11152680490922118018828689)
          ·
            refine ⟨8364510368191588514121517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11152680490922118018828689 8364510368191588514121517)
            ·
              refine ⟨3136691388071845692795569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8364510368191588514121517 3136691388071845692795569)
              ·
                refine ⟨2352518541053884269596677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3136691388071845692795569 2352518541053884269596677)
                ·
                  refine ⟨441097226447603300549377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352518541053884269596677 441097226447603300549377)
                  ·
                    rfl

theorem cell22_3865652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3865652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865652 prefixEnd_3865652 := by exact prefixLift 3865652
  have htrace : WordTrace (prefixWord ++ tailWord_3865652) baseStart_3865652 baseEnd_3865652 := by
    simpa [prefixWord, tailWord_3865652, baseEnd_3865652] using wordTrace_append hprefix tailTrace_3865652
  have hstable : (prefixWord ++ tailWord_3865652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865652).length < 2 ^ (prefixWord ++ tailWord_3865652).sum := by decide
  have hdescent : baseEnd_3865652 < baseStart_3865652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865689 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_3865689 : Nat := 118140960795 + 3865689 * 2 ^ 59
def prefixEnd_3865689 : Nat := 4983230072969 + 3 ^ 40 * 3865689 * 2
def baseEnd_3865689 : Nat := 1323304345198954138473017

theorem tailTrace_3865689 : CollatzResearch.WordTrace tailWord_3865689 prefixEnd_3865689 1323304345198954138473017 := by
  unfold tailWord_3865689
  simp only [CollatzResearch.WordTrace]
  refine ⟨140993260892276434964536121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93995507261517623309690747 140993260892276434964536121)
  ·
    refine ⟨105744945669207326223402091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140993260892276434964536121 105744945669207326223402091)
    ·
      refine ⟨158617418503810989335103137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105744945669207326223402091 158617418503810989335103137)
      ·
        refine ⟨118963063877858242001327353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158617418503810989335103137 118963063877858242001327353)
        ·
          refine ⟨89222297908393681500995515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118963063877858242001327353 89222297908393681500995515)
          ·
            refine ⟨133833446862590522251493273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89222297908393681500995515 133833446862590522251493273)
            ·
              refine ⟨100375085146942891688619955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133833446862590522251493273 100375085146942891688619955)
              ·
                refine ⟨150562627720414337532929933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100375085146942891688619955 150562627720414337532929933)
                ·
                  refine ⟨56460985395155376574848725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150562627720414337532929933 56460985395155376574848725)
                  ·
                    refine ⟨1323304345198954138473017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56460985395155376574848725 1323304345198954138473017)
                    ·
                      rfl

theorem cell22_3865689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_3865689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865689 prefixEnd_3865689 := by exact prefixLift 3865689
  have htrace : WordTrace (prefixWord ++ tailWord_3865689) baseStart_3865689 baseEnd_3865689 := by
    simpa [prefixWord, tailWord_3865689, baseEnd_3865689] using wordTrace_append hprefix tailTrace_3865689
  have hstable : (prefixWord ++ tailWord_3865689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865689).length < 2 ^ (prefixWord ++ tailWord_3865689).sum := by decide
  have hdescent : baseEnd_3865689 < baseStart_3865689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865738 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3865738 : Nat := 118140960795 + 3865738 * 2 ^ 59
def prefixEnd_3865738 : Nat := 4983230072969 + 3 ^ 40 * 3865738 * 2
def baseEnd_3865738 : Nat := 1323321118900334343997867

theorem tailTrace_3865738 : CollatzResearch.WordTrace tailWord_3865738 prefixEnd_3865738 1323321118900334343997867 := by
  unfold tailWord_3865738
  simp only [CollatzResearch.WordTrace]
  refine ⟨35248762017274729083267467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93996698712732610888713245 35248762017274729083267467)
  ·
    refine ⟨52873143025912093624901201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35248762017274729083267467 52873143025912093624901201)
    ·
      refine ⟨39654857269434070218675901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52873143025912093624901201 39654857269434070218675901)
      ·
        refine ⟨14870571476037776332003463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39654857269434070218675901 14870571476037776332003463)
        ·
          refine ⟨22305857214056664498005195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14870571476037776332003463 22305857214056664498005195)
          ·
            refine ⟨33458785821084996747007793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22305857214056664498005195 33458785821084996747007793)
            ·
              refine ⟨25094089365813747560255845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33458785821084996747007793 25094089365813747560255845)
              ·
                refine ⟨4705141756090077667547971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25094089365813747560255845 4705141756090077667547971)
                ·
                  refine ⟨7057712634135116501321957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705141756090077667547971 7057712634135116501321957)
                  ·
                    refine ⟨1323321118900334343997867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7057712634135116501321957 1323321118900334343997867)
                    ·
                      rfl

theorem cell22_3865738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3865738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865738 prefixEnd_3865738 := by exact prefixLift 3865738
  have htrace : WordTrace (prefixWord ++ tailWord_3865738) baseStart_3865738 baseEnd_3865738 := by
    simpa [prefixWord, tailWord_3865738, baseEnd_3865738] using wordTrace_append hprefix tailTrace_3865738
  have hstable : (prefixWord ++ tailWord_3865738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865738).length < 2 ^ (prefixWord ++ tailWord_3865738).sum := by decide
  have hdescent : baseEnd_3865738 < baseStart_3865738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865770 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_3865770 : Nat := 118140960795 + 3865770 * 2 ^ 59
def prefixEnd_3865770 : Nat := 4983230072969 + 3 ^ 40 * 3865770 * 2
def baseEnd_3865770 : Nat := 441110691051432309065923

theorem tailTrace_3865770 : CollatzResearch.WordTrace tailWord_3865770 prefixEnd_3865770 441110691051432309065923 := by
  unfold tailWord_3865770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35249053801245746449558691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93997476803321990532156509 35249053801245746449558691)
  ·
    refine ⟨52873580701868619674338037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35249053801245746449558691 52873580701868619674338037)
    ·
      refine ⟨4956898190800183094469191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52873580701868619674338037 4956898190800183094469191)
      ·
        refine ⟨7435347286200274641703787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956898190800183094469191 7435347286200274641703787)
        ·
          refine ⟨11153020929300411962555681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435347286200274641703787 11153020929300411962555681)
          ·
            refine ⟨8364765696975308971916761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11153020929300411962555681 8364765696975308971916761)
            ·
              refine ⟨6273574272731481728937571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8364765696975308971916761 6273574272731481728937571)
              ·
                refine ⟨9410361409097222593406357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273574272731481728937571 9410361409097222593406357)
                ·
                  refine ⟨441110691051432309065923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9410361409097222593406357 441110691051432309065923)
                  ·
                    rfl

theorem cell22_3865770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_3865770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865770 prefixEnd_3865770 := by exact prefixLift 3865770
  have htrace : WordTrace (prefixWord ++ tailWord_3865770) baseStart_3865770 baseEnd_3865770 := by
    simpa [prefixWord, tailWord_3865770, baseEnd_3865770] using wordTrace_append hprefix tailTrace_3865770
  have hstable : (prefixWord ++ tailWord_3865770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865770).length < 2 ^ (prefixWord ++ tailWord_3865770).sum := by decide
  have hdescent : baseEnd_3865770 < baseStart_3865770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865841 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_3865841 : Nat := 118140960795 + 3865841 * 2 ^ 59
def prefixEnd_3865841 : Nat := 4983230072969 + 3 ^ 40 * 3865841 * 2
def baseEnd_3865841 : Nat := 1323356377905276408672551

theorem tailTrace_3865841 : CollatzResearch.WordTrace tailWord_3865841 prefixEnd_3865841 1323356377905276408672551 := by
  unfold tailWord_3865841
  simp only [CollatzResearch.WordTrace]
  refine ⟨140998804787725764924069377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93999203191817176616046251 140998804787725764924069377)
  ·
    refine ⟨105749103590794323693052033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140998804787725764924069377 105749103590794323693052033)
    ·
      refine ⟨79311827693095742769789025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105749103590794323693052033 79311827693095742769789025)
      ·
        refine ⟨59483870769821807077341769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79311827693095742769789025 59483870769821807077341769)
        ·
          refine ⟨44612903077366355308006327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59483870769821807077341769 44612903077366355308006327)
          ·
            refine ⟨66919354616049532962009491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44612903077366355308006327 66919354616049532962009491)
            ·
              refine ⟨100379031924074299443014237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66919354616049532962009491 100379031924074299443014237)
              ·
                refine ⟨37642136971527862291130339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100379031924074299443014237 37642136971527862291130339)
                ·
                  refine ⟨56463205457291793436695509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37642136971527862291130339 56463205457291793436695509)
                  ·
                    refine ⟨1323356377905276408672551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56463205457291793436695509 1323356377905276408672551)
                    ·
                      rfl

theorem cell22_3865841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_3865841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865841 prefixEnd_3865841 := by exact prefixLift 3865841
  have htrace : WordTrace (prefixWord ++ tailWord_3865841) baseStart_3865841 baseEnd_3865841 := by
    simpa [prefixWord, tailWord_3865841, baseEnd_3865841] using wordTrace_append hprefix tailTrace_3865841
  have hstable : (prefixWord ++ tailWord_3865841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865841).length < 2 ^ (prefixWord ++ tailWord_3865841).sum := by decide
  have hdescent : baseEnd_3865841 < baseStart_3865841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865843 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 5]
def baseStart_3865843 : Nat := 118140960795 + 3865843 * 2 ^ 59
def prefixEnd_3865843 : Nat := 4983230072969 + 3 ^ 40 * 3865843 * 2
def baseEnd_3865843 : Nat := 441119020848716356707515

theorem tailTrace_3865843 : CollatzResearch.WordTrace tailWord_3865843 prefixEnd_3865843 441119020848716356707515 := by
  unfold tailWord_3865843
  simp only [CollatzResearch.WordTrace]
  refine ⟨140998877733718519265642183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93999251822479012843761455 140998877733718519265642183)
  ·
    refine ⟨211498316600577778898463275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140998877733718519265642183 211498316600577778898463275)
    ·
      refine ⟨317247474900866668347694913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211498316600577778898463275 317247474900866668347694913)
      ·
        refine ⟨237935606175650001260771185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317247474900866668347694913 237935606175650001260771185)
        ·
          refine ⟨178451704631737500945578389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237935606175650001260771185 178451704631737500945578389)
          ·
            refine ⟨8364923654612695356823987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178451704631737500945578389 8364923654612695356823987)
            ·
              refine ⟨12547385481919043035235981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364923654612695356823987 12547385481919043035235981)
              ·
                refine ⟨4705269555719641138213493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12547385481919043035235981 4705269555719641138213493)
                ·
                  refine ⟨441119020848716356707515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4705269555719641138213493 441119020848716356707515)
                  ·
                    rfl

theorem cell22_3865843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 5].length) (baseStart_3865843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865843 prefixEnd_3865843 := by exact prefixLift 3865843
  have htrace : WordTrace (prefixWord ++ tailWord_3865843) baseStart_3865843 baseEnd_3865843 := by
    simpa [prefixWord, tailWord_3865843, baseEnd_3865843] using wordTrace_append hprefix tailTrace_3865843
  have hstable : (prefixWord ++ tailWord_3865843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865843).length < 2 ^ (prefixWord ++ tailWord_3865843).sum := by decide
  have hdescent : baseEnd_3865843 < baseStart_3865843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865903 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 6, 3]
def baseStart_3865903 : Nat := 118140960795 + 3865903 * 2 ^ 59
def prefixEnd_3865903 : Nat := 4983230072969 + 3 ^ 40 * 3865903 * 2
def baseEnd_3865903 : Nat := 1323377601772328913622361

theorem tailTrace_3865903 : CollatzResearch.WordTrace tailWord_3865903 prefixEnd_3865903 1323377601772328913622361 := by
  unfold tailWord_3865903
  simp only [CollatzResearch.WordTrace]
  refine ⟨141001066113501149512826363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94000710742334099675217575 141001066113501149512826363)
  ·
    refine ⟨211501599170251724269239545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141001066113501149512826363 211501599170251724269239545)
    ·
      refine ⟨158626199377688793201929659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211501599170251724269239545 158626199377688793201929659)
      ·
        refine ⟨237939299066533189802894489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158626199377688793201929659 237939299066533189802894489)
        ·
          refine ⟨178454474299899892352170867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237939299066533189802894489 178454474299899892352170867)
          ·
            refine ⟨267681711449849838528256301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178454474299899892352170867 267681711449849838528256301)
            ·
              refine ⟨100380641793693689448096113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267681711449849838528256301 100380641793693689448096113)
              ·
                refine ⟨75285481345270267086072085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100380641793693689448096113 75285481345270267086072085)
                ·
                  refine ⟨3529006938059543769659629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75285481345270267086072085 3529006938059543769659629)
                  ·
                    refine ⟨1323377601772328913622361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529006938059543769659629 1323377601772328913622361)
                    ·
                      rfl

theorem cell22_3865903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_3865903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865903 prefixEnd_3865903 := by exact prefixLift 3865903
  have htrace : WordTrace (prefixWord ++ tailWord_3865903) baseStart_3865903 baseEnd_3865903 := by
    simpa [prefixWord, tailWord_3865903, baseEnd_3865903] using wordTrace_append hprefix tailTrace_3865903
  have hstable : (prefixWord ++ tailWord_3865903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865903).length < 2 ^ (prefixWord ++ tailWord_3865903).sum := by decide
  have hdescent : baseEnd_3865903 < baseStart_3865903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865924 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3865924 : Nat := 118140960795 + 3865924 * 2 ^ 59
def prefixEnd_3865924 : Nat := 4983230072969 + 3 ^ 40 * 3865924 * 2
def baseEnd_3865924 : Nat := 1323384790501491858847297

theorem tailTrace_3865924 : CollatzResearch.WordTrace tailWord_3865924 prefixEnd_3865924 1323384790501491858847297 := by
  unfold tailWord_3865924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70500916023212535049670413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94001221364283380066227217 70500916023212535049670413)
  ·
    refine ⟨26437843508704700643626405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70500916023212535049670413 26437843508704700643626405)
    ·
      refine ⟨4957095657882131370679951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26437843508704700643626405 4957095657882131370679951)
      ·
        refine ⟨7435643486823197056019927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957095657882131370679951 7435643486823197056019927)
        ·
          refine ⟨11153465230234795584029891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435643486823197056019927 11153465230234795584029891)
          ·
            refine ⟨16730197845352193376044837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11153465230234795584029891 16730197845352193376044837)
            ·
              refine ⟨3136912096003536258008407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16730197845352193376044837 3136912096003536258008407)
              ·
                refine ⟨4705368144005304387012611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136912096003536258008407 4705368144005304387012611)
                ·
                  refine ⟨7058052216007956580518917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705368144005304387012611 7058052216007956580518917)
                  ·
                    refine ⟨1323384790501491858847297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058052216007956580518917 1323384790501491858847297)
                    ·
                      rfl

theorem cell22_3865924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3865924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865924 prefixEnd_3865924 := by exact prefixLift 3865924
  have htrace : WordTrace (prefixWord ++ tailWord_3865924) baseStart_3865924 baseEnd_3865924 := by
    simpa [prefixWord, tailWord_3865924, baseEnd_3865924] using wordTrace_append hprefix tailTrace_3865924
  have hstable : (prefixWord ++ tailWord_3865924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865924).length < 2 ^ (prefixWord ++ tailWord_3865924).sum := by decide
  have hdescent : baseEnd_3865924 < baseStart_3865924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865954 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3865954 : Nat := 118140960795 + 3865954 * 2 ^ 59
def prefixEnd_3865954 : Nat := 4983230072969 + 3 ^ 40 * 3865954 * 2
def baseEnd_3865954 : Nat := 1323395060114581780597205

theorem tailTrace_3865954 : CollatzResearch.WordTrace tailWord_3865954 prefixEnd_3865954 1323395060114581780597205 := by
  unfold tailWord_3865954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35250731559079096305733229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94001950824210923481955277 35250731559079096305733229)
  ·
    refine ⟨13219024334654661114649961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35250731559079096305733229 13219024334654661114649961)
    ·
      refine ⟨9914268250990995835987471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13219024334654661114649961 9914268250990995835987471)
      ·
        refine ⟨14871402376486493753981207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914268250990995835987471 14871402376486493753981207)
        ·
          refine ⟨22307103564729740630971811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14871402376486493753981207 22307103564729740630971811)
          ·
            refine ⟨33460655347094610946457717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22307103564729740630971811 33460655347094610946457717)
            ·
              refine ⟨3136936438790119776230411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33460655347094610946457717 3136936438790119776230411)
              ·
                refine ⟨4705404658185179664345617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136936438790119776230411 4705404658185179664345617)
                ·
                  refine ⟨3529053493638884748259213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4705404658185179664345617 3529053493638884748259213)
                  ·
                    refine ⟨1323395060114581780597205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529053493638884748259213 1323395060114581780597205)
                    ·
                      rfl

theorem cell22_3865954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3865954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3865954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3865954 prefixEnd_3865954 := by exact prefixLift 3865954
  have htrace : WordTrace (prefixWord ++ tailWord_3865954) baseStart_3865954 baseEnd_3865954 := by
    simpa [prefixWord, tailWord_3865954, baseEnd_3865954] using wordTrace_append hprefix tailTrace_3865954
  have hstable : (prefixWord ++ tailWord_3865954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865954).length < 2 ^ (prefixWord ++ tailWord_3865954).sum := by decide
  have hdescent : baseEnd_3865954 < baseStart_3865954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866072 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_3866072 : Nat := 118140960795 + 3866072 * 2 ^ 59
def prefixEnd_3866072 : Nat := 4983230072969 + 3 ^ 40 * 3866072 * 2
def baseEnd_3866072 : Nat := 1323435453926068806146843

theorem tailTrace_3866072 : CollatzResearch.WordTrace tailWord_3866072 prefixEnd_3866072 1323435453926068806146843 := by
  unfold tailWord_3866072
  simp only [CollatzResearch.WordTrace]
  refine ⟨70503615024944445687864235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94004820033259260917152313 70503615024944445687864235)
  ·
    refine ⟨105755422537416668531796353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70503615024944445687864235 105755422537416668531796353)
    ·
      refine ⟨79316566903062501398847265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105755422537416668531796353 79316566903062501398847265)
      ·
        refine ⟨59487425177296876049135449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79316566903062501398847265 59487425177296876049135449)
        ·
          refine ⟨44615568882972657036851587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59487425177296876049135449 44615568882972657036851587)
          ·
            refine ⟨66923353324458985555277381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44615568882972657036851587 66923353324458985555277381)
            ·
              refine ⟨12548128748336059791614509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66923353324458985555277381 12548128748336059791614509)
              ·
                refine ⟨4705548280626022421855441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12548128748336059791614509 4705548280626022421855441)
                ·
                  refine ⟨3529161210469516816391581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4705548280626022421855441 3529161210469516816391581)
                  ·
                    refine ⟨1323435453926068806146843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529161210469516816391581 1323435453926068806146843)
                    ·
                      rfl

theorem cell22_3866072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_3866072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866072 prefixEnd_3866072 := by exact prefixLift 3866072
  have htrace : WordTrace (prefixWord ++ tailWord_3866072) baseStart_3866072 baseEnd_3866072 := by
    simpa [prefixWord, tailWord_3866072, baseEnd_3866072] using wordTrace_append hprefix tailTrace_3866072
  have hstable : (prefixWord ++ tailWord_3866072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866072).length < 2 ^ (prefixWord ++ tailWord_3866072).sum := by decide
  have hdescent : baseEnd_3866072 < baseStart_3866072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866087 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3866087 : Nat := 118140960795 + 3866087 * 2 ^ 59
def prefixEnd_3866087 : Nat := 4983230072969 + 3 ^ 40 * 3866087 * 2
def baseEnd_3866087 : Nat := 1323440588732613767021797

theorem tailTrace_3866087 : CollatzResearch.WordTrace tailWord_3866087 prefixEnd_3866087 1323440588732613767021797 := by
  unfold tailWord_3866087
  simp only [CollatzResearch.WordTrace]
  refine ⟨141007777144834548937524515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94005184763223032625016343 141007777144834548937524515)
  ·
    refine ⟨211511665717251823406286773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141007777144834548937524515 211511665717251823406286773)
    ·
      refine ⟨19829218660992358444339385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211511665717251823406286773 19829218660992358444339385)
      ·
        refine ⟨14871913995744268833254539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19829218660992358444339385 14871913995744268833254539)
        ·
          refine ⟨22307870993616403249881809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14871913995744268833254539 22307870993616403249881809)
          ·
            refine ⟨16730903245212302437411357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22307870993616403249881809 16730903245212302437411357)
            ·
              refine ⟨6274088716954613414029259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16730903245212302437411357 6274088716954613414029259)
              ·
                refine ⟨9411133075431920121043889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274088716954613414029259 9411133075431920121043889)
                ·
                  refine ⟨7058349806573940090782917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411133075431920121043889 7058349806573940090782917)
                  ·
                    refine ⟨1323440588732613767021797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058349806573940090782917 1323440588732613767021797)
                    ·
                      rfl

theorem cell22_3866087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3866087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866087 prefixEnd_3866087 := by exact prefixLift 3866087
  have htrace : WordTrace (prefixWord ++ tailWord_3866087) baseStart_3866087 baseEnd_3866087 := by
    simpa [prefixWord, tailWord_3866087, baseEnd_3866087] using wordTrace_append hprefix tailTrace_3866087
  have hstable : (prefixWord ++ tailWord_3866087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866087).length < 2 ^ (prefixWord ++ tailWord_3866087).sum := by decide
  have hdescent : baseEnd_3866087 < baseStart_3866087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866093 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_3866093 : Nat := 118140960795 + 3866093 * 2 ^ 59
def prefixEnd_3866093 : Nat := 4983230072969 + 3 ^ 40 * 3866093 * 2
def baseEnd_3866093 : Nat := 1323442642655231751371779

theorem tailTrace_3866093 : CollatzResearch.WordTrace tailWord_3866093 prefixEnd_3866093 1323442642655231751371779 := by
  unfold tailWord_3866093
  simp only [CollatzResearch.WordTrace]
  refine ⟨141007995982812811962242933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94005330655208541308161955 141007995982812811962242933)
  ·
    refine ⟨13219499623388701121460275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141007995982812811962242933 13219499623388701121460275)
    ·
      refine ⟨19829249435083051682190413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13219499623388701121460275 19829249435083051682190413)
      ·
        refine ⟨7435968538156144380821405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19829249435083051682190413 7435968538156144380821405)
        ·
          refine ⟨2788488201808554142808027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7435968538156144380821405 2788488201808554142808027)
          ·
            refine ⟨4182732302712831214212041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788488201808554142808027 4182732302712831214212041)
            ·
              refine ⟨3137049227034623410659031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182732302712831214212041 3137049227034623410659031)
              ·
                refine ⟨4705573840551935115988547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137049227034623410659031 4705573840551935115988547)
                ·
                  refine ⟨7058360760827902673982821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705573840551935115988547 7058360760827902673982821)
                  ·
                    refine ⟨1323442642655231751371779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058360760827902673982821 1323442642655231751371779)
                    ·
                      rfl

theorem cell22_3866093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_3866093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866093 prefixEnd_3866093 := by exact prefixLift 3866093
  have htrace : WordTrace (prefixWord ++ tailWord_3866093) baseStart_3866093 baseEnd_3866093 := by
    simpa [prefixWord, tailWord_3866093, baseEnd_3866093] using wordTrace_append hprefix tailTrace_3866093
  have hstable : (prefixWord ++ tailWord_3866093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866093).length < 2 ^ (prefixWord ++ tailWord_3866093).sum := by decide
  have hdescent : baseEnd_3866093 < baseStart_3866093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866142 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3866142 : Nat := 118140960795 + 3866142 * 2 ^ 59
def prefixEnd_3866142 : Nat := 4983230072969 + 3 ^ 40 * 3866142 * 2
def baseEnd_3866142 : Nat := 441153138785537318965543

theorem tailTrace_3866142 : CollatzResearch.WordTrace tailWord_3866142 prefixEnd_3866142 441153138785537318965543 := by
  unfold tailWord_3866142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626222894954411666347085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94006522106423528887184453 17626222894954411666347085)
  ·
    refine ⟨6609833585607904374880157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17626222894954411666347085 6609833585607904374880157)
    ·
      refine ⟨2478687594602964140580059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6609833585607904374880157 2478687594602964140580059)
      ·
        refine ⟨3718031391904446210870089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478687594602964140580059 3718031391904446210870089)
        ·
          refine ⟨2788523543928334658152567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3718031391904446210870089 2788523543928334658152567)
          ·
            refine ⟨4182785315892501987228851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788523543928334658152567 4182785315892501987228851)
            ·
              refine ⟨6274177973838752980843277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182785315892501987228851 6274177973838752980843277)
              ·
                refine ⟨2352816740189532367816229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6274177973838752980843277 2352816740189532367816229)
                ·
                  refine ⟨441153138785537318965543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352816740189532367816229 441153138785537318965543)
                  ·
                    rfl

theorem cell22_3866142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3866142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866142 prefixEnd_3866142 := by exact prefixLift 3866142
  have htrace : WordTrace (prefixWord ++ tailWord_3866142) baseStart_3866142 baseEnd_3866142 := by
    simpa [prefixWord, tailWord_3866142, baseEnd_3866142] using wordTrace_append hprefix tailTrace_3866142
  have hstable : (prefixWord ++ tailWord_3866142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866142).length < 2 ^ (prefixWord ++ tailWord_3866142).sum := by decide
  have hdescent : baseEnd_3866142 < baseStart_3866142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866160 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_3866160 : Nat := 118140960795 + 3866160 * 2 ^ 59
def prefixEnd_3866160 : Nat := 4983230072969 + 3 ^ 40 * 3866160 * 2
def baseEnd_3866160 : Nat := 1323465578124465909946573

theorem tailTrace_3866160 : CollatzResearch.WordTrace tailWord_3866160 prefixEnd_3866160 1323465578124465909946573 := by
  unfold tailWord_3866160
  simp only [CollatzResearch.WordTrace]
  refine ⟨70505219836785041202465967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94006959782380054936621289 70505219836785041202465967)
  ·
    refine ⟨105757829755177561803698951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70505219836785041202465967 105757829755177561803698951)
    ·
      refine ⟨158636744632766342705548427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105757829755177561803698951 158636744632766342705548427)
      ·
        refine ⟨237955116949149514058322641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158636744632766342705548427 237955116949149514058322641)
        ·
          refine ⟨178466337711862135543741981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237955116949149514058322641 178466337711862135543741981)
          ·
            refine ⟨66924876641948300828903243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178466337711862135543741981 66924876641948300828903243)
            ·
              refine ⟨100387314962922451243354865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66924876641948300828903243 100387314962922451243354865)
              ·
                refine ⟨75290486222191838432516149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100387314962922451243354865 75290486222191838432516149)
                ·
                  refine ⟨7058483083330484853048389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75290486222191838432516149 7058483083330484853048389)
                  ·
                    refine ⟨1323465578124465909946573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058483083330484853048389 1323465578124465909946573)
                    ·
                      rfl

theorem cell22_3866160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_3866160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866160 prefixEnd_3866160 := by exact prefixLift 3866160
  have htrace : WordTrace (prefixWord ++ tailWord_3866160) baseStart_3866160 baseEnd_3866160 := by
    simpa [prefixWord, tailWord_3866160, baseEnd_3866160] using wordTrace_append hprefix tailTrace_3866160
  have hstable : (prefixWord ++ tailWord_3866160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866160).length < 2 ^ (prefixWord ++ tailWord_3866160).sum := by decide
  have hdescent : baseEnd_3866160 < baseStart_3866160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866177 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3866177 : Nat := 118140960795 + 3866177 * 2 ^ 59
def prefixEnd_3866177 : Nat := 4983230072969 + 3 ^ 40 * 3866177 * 2
def baseEnd_3866177 : Nat := 1323471397571883532271521

theorem tailTrace_3866177 : CollatzResearch.WordTrace tailWord_3866177 prefixEnd_3866177 1323471397571883532271521 := by
  unfold tailWord_3866177
  simp only [CollatzResearch.WordTrace]
  refine ⟨141011059714508494308300785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94007373143005662872200523 141011059714508494308300785)
  ·
    refine ⟨105758294785881370731225589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141011059714508494308300785 105758294785881370731225589)
    ·
      refine ⟨9914840136176378506052399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105758294785881370731225589 9914840136176378506052399)
      ·
        refine ⟨14872260204264567759078599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914840136176378506052399 14872260204264567759078599)
        ·
          refine ⟨22308390306396851638617899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872260204264567759078599 22308390306396851638617899)
          ·
            refine ⟨33462585459595277457926849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22308390306396851638617899 33462585459595277457926849)
            ·
              refine ⟨25096939094696458093445137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33462585459595277457926849 25096939094696458093445137)
              ·
                refine ⟨18822704321022343570083853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25096939094696458093445137 18822704321022343570083853)
                ·
                  refine ⟨7058514120383378838781445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18822704321022343570083853 7058514120383378838781445)
                  ·
                    refine ⟨1323471397571883532271521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058514120383378838781445 1323471397571883532271521)
                    ·
                      rfl

theorem cell22_3866177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3866177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866177 prefixEnd_3866177 := by exact prefixLift 3866177
  have htrace : WordTrace (prefixWord ++ tailWord_3866177) baseStart_3866177 baseEnd_3866177 := by
    simpa [prefixWord, tailWord_3866177, baseEnd_3866177] using wordTrace_append hprefix tailTrace_3866177
  have hstable : (prefixWord ++ tailWord_3866177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866177).length < 2 ^ (prefixWord ++ tailWord_3866177).sum := by decide
  have hdescent : baseEnd_3866177 < baseStart_3866177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866194 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3866194 : Nat := 118140960795 + 3866194 * 2 ^ 59
def prefixEnd_3866194 : Nat := 4983230072969 + 3 ^ 40 * 3866194 * 2
def baseEnd_3866194 : Nat := 1323477217019301154596469

theorem tailTrace_3866194 : CollatzResearch.WordTrace tailWord_3866194 prefixEnd_3866194 1323477217019301154596469 := by
  unfold tailWord_3866194
  simp only [CollatzResearch.WordTrace]
  refine ⟨35252919938861726552917409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94007786503631270807779757 35252919938861726552917409)
  ·
    refine ⟨26439689954146294914688057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35252919938861726552917409 26439689954146294914688057)
    ·
      refine ⟨19829767465609721186016043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26439689954146294914688057 19829767465609721186016043)
      ·
        refine ⟨29744651198414581779024065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19829767465609721186016043 29744651198414581779024065)
        ·
          refine ⟨22308488398810936334268049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29744651198414581779024065 22308488398810936334268049)
          ·
            refine ⟨16731366299108202250701037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22308488398810936334268049 16731366299108202250701037)
            ·
              refine ⟨6274262362165575844012889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16731366299108202250701037 6274262362165575844012889)
              ·
                refine ⟨4705696771624181883009667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6274262362165575844012889 4705696771624181883009667)
                ·
                  refine ⟨7058545157436272824514501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705696771624181883009667 7058545157436272824514501)
                  ·
                    refine ⟨1323477217019301154596469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058545157436272824514501 1323477217019301154596469)
                    ·
                      rfl

theorem cell22_3866194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3866194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866194 prefixEnd_3866194 := by exact prefixLift 3866194
  have htrace : WordTrace (prefixWord ++ tailWord_3866194) baseStart_3866194 baseEnd_3866194 := by
    simpa [prefixWord, tailWord_3866194, baseEnd_3866194] using wordTrace_append hprefix tailTrace_3866194
  have hstable : (prefixWord ++ tailWord_3866194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866194).length < 2 ^ (prefixWord ++ tailWord_3866194).sum := by decide
  have hdescent : baseEnd_3866194 < baseStart_3866194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866224 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_3866224 : Nat := 118140960795 + 3866224 * 2 ^ 59
def prefixEnd_3866224 : Nat := 4983230072969 + 3 ^ 40 * 3866224 * 2
def baseEnd_3866224 : Nat := 1323487486632391076346377

theorem tailTrace_3866224 : CollatzResearch.WordTrace tailWord_3866224 prefixEnd_3866224 1323487486632391076346377 := by
  unfold tailWord_3866224
  simp only [CollatzResearch.WordTrace]
  refine ⟨70506386972669110667630863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94008515963558814223507817 70506386972669110667630863)
  ·
    refine ⟨105759580459003666001446295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70506386972669110667630863 105759580459003666001446295)
    ·
      refine ⟨158639370688505499002169443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105759580459003666001446295 158639370688505499002169443)
      ·
        refine ⟨237959056032758248503254165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158639370688505499002169443 237959056032758248503254165)
        ·
          refine ⟨11154330751535542898590039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237959056032758248503254165 11154330751535542898590039)
          ·
            refine ⟨16731496127303314347885059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154330751535542898590039 16731496127303314347885059)
            ·
              refine ⟨25097244190954971521827589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16731496127303314347885059 25097244190954971521827589)
              ·
                refine ⟨4705733285804057160342673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25097244190954971521827589 4705733285804057160342673)
                ·
                  refine ⟨3529299964353042870257005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4705733285804057160342673 3529299964353042870257005)
                  ·
                    refine ⟨1323487486632391076346377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529299964353042870257005 1323487486632391076346377)
                    ·
                      rfl

theorem cell22_3866224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_3866224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866224 prefixEnd_3866224 := by exact prefixLift 3866224
  have htrace : WordTrace (prefixWord ++ tailWord_3866224) baseStart_3866224 baseEnd_3866224 := by
    simpa [prefixWord, tailWord_3866224, baseEnd_3866224] using wordTrace_append hprefix tailTrace_3866224
  have hstable : (prefixWord ++ tailWord_3866224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866224).length < 2 ^ (prefixWord ++ tailWord_3866224).sum := by decide
  have hdescent : baseEnd_3866224 < baseStart_3866224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866226 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_3866226 : Nat := 118140960795 + 3866226 * 2 ^ 59
def prefixEnd_3866226 : Nat := 4983230072969 + 3 ^ 40 * 3866226 * 2
def baseEnd_3866226 : Nat := 441162723757754579265457

theorem tailTrace_3866226 : CollatzResearch.WordTrace tailWord_3866226 prefixEnd_3866226 441162723757754579265457 := by
  unfold tailWord_3866226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35253211722832743919208633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94008564594220650451223021 35253211722832743919208633)
  ·
    refine ⟨26439908792124557939406475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35253211722832743919208633 26439908792124557939406475)
    ·
      refine ⟨39659863188186836909109713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26439908792124557939406475 39659863188186836909109713)
      ·
        refine ⟨29744897391140127681832285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39659863188186836909109713 29744897391140127681832285)
        ·
          refine ⟨11154336521677547880687107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29744897391140127681832285 11154336521677547880687107)
          ·
            refine ⟨16731504782516321821030661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154336521677547880687107 16731504782516321821030661)
            ·
              refine ⟨3137157146721810341443249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16731504782516321821030661 3137157146721810341443249)
              ·
                refine ⟨2352867860041357756082437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137157146721810341443249 2352867860041357756082437)
                ·
                  refine ⟨441162723757754579265457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352867860041357756082437 441162723757754579265457)
                  ·
                    rfl

theorem cell22_3866226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_3866226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866226 prefixEnd_3866226 := by exact prefixLift 3866226
  have htrace : WordTrace (prefixWord ++ tailWord_3866226) baseStart_3866226 baseEnd_3866226 := by
    simpa [prefixWord, tailWord_3866226, baseEnd_3866226] using wordTrace_append hprefix tailTrace_3866226
  have hstable : (prefixWord ++ tailWord_3866226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866226).length < 2 ^ (prefixWord ++ tailWord_3866226).sum := by decide
  have hdescent : baseEnd_3866226 < baseStart_3866226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866237 : List Nat := [1, 4, 1, 1, 4, 1, 3, 7]
def baseStart_3866237 : Nat := 118140960795 + 3866237 * 2 ^ 59
def prefixEnd_3866237 : Nat := 4983230072969 + 3 ^ 40 * 3866237 * 2
def baseEnd_3866237 : Nat := 147054659644229263974593

theorem tailTrace_3866237 : CollatzResearch.WordTrace tailWord_3866237 prefixEnd_3866237 147054659644229263974593 := by
  unfold tailWord_3866237
  simp only [CollatzResearch.WordTrace]
  refine ⟨141013248094291124555484965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94008832062860749703656643 141013248094291124555484965)
  ·
    refine ⟨26439984017679585854153431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141013248094291124555484965 26439984017679585854153431)
    ·
      refine ⟨39659976026519378781230147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26439984017679585854153431 39659976026519378781230147)
      ·
        refine ⟨59489964039779068171845221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39659976026519378781230147 59489964039779068171845221)
        ·
          refine ⟨11154368257458575282220979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59489964039779068171845221 11154368257458575282220979)
          ·
            refine ⟨16731552386187862923331469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154368257458575282220979 16731552386187862923331469)
            ·
              refine ⟨6274332144820448596249301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16731552386187862923331469 6274332144820448596249301)
              ·
                refine ⟨147054659644229263974593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6274332144820448596249301 147054659644229263974593)
                ·
                  rfl

theorem cell22_3866237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 7].length) (baseStart_3866237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866237 prefixEnd_3866237 := by exact prefixLift 3866237
  have htrace : WordTrace (prefixWord ++ tailWord_3866237) baseStart_3866237 baseEnd_3866237 := by
    simpa [prefixWord, tailWord_3866237, baseEnd_3866237] using wordTrace_append hprefix tailTrace_3866237
  have hstable : (prefixWord ++ tailWord_3866237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866237).length < 2 ^ (prefixWord ++ tailWord_3866237).sum := by decide
  have hdescent : baseEnd_3866237 < baseStart_3866237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866254 : List Nat := [4, 1, 1, 3, 1, 3, 3, 6]
def baseStart_3866254 : Nat := 118140960795 + 3866254 * 2 ^ 59
def prefixEnd_3866254 : Nat := 4983230072969 + 3 ^ 40 * 3866254 * 2
def baseEnd_3866254 : Nat := 147055306249497888677365

theorem tailTrace_3866254 : CollatzResearch.WordTrace tailWord_3866254 prefixEnd_3866254 147055306249497888677365 := by
  unfold tailWord_3866254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626733516903692057356727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94009245423486357639235877 17626733516903692057356727)
  ·
    refine ⟨26440100275355538086035091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17626733516903692057356727 26440100275355538086035091)
    ·
      refine ⟨39660150413033307129052637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26440100275355538086035091 39660150413033307129052637)
      ·
        refine ⟨14872556404887490173394739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39660150413033307129052637 14872556404887490173394739)
        ·
          refine ⟨22308834607331235260092109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872556404887490173394739 22308834607331235260092109)
          ·
            refine ⟨8365812977749213222534541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22308834607331235260092109 8365812977749213222534541)
            ·
              refine ⟨3137179866655954958450453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8365812977749213222534541 3137179866655954958450453)
              ·
                refine ⟨147055306249497888677365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3137179866655954958450453 147055306249497888677365)
                ·
                  rfl

theorem cell22_3866254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_3866254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866254 prefixEnd_3866254 := by exact prefixLift 3866254
  have htrace : WordTrace (prefixWord ++ tailWord_3866254) baseStart_3866254 baseEnd_3866254 := by
    simpa [prefixWord, tailWord_3866254, baseEnd_3866254] using wordTrace_append hprefix tailTrace_3866254
  have hstable : (prefixWord ++ tailWord_3866254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866254).length < 2 ^ (prefixWord ++ tailWord_3866254).sum := by decide
  have hdescent : baseEnd_3866254 < baseStart_3866254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866297 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_3866297 : Nat := 118140960795 + 3866297 * 2 ^ 59
def prefixEnd_3866297 : Nat := 4983230072969 + 3 ^ 40 * 3866297 * 2
def baseEnd_3866297 : Nat := 1323512476024243219271153

theorem tailTrace_3866297 : CollatzResearch.WordTrace tailWord_3866297 prefixEnd_3866297 1323512476024243219271153 := by
  unfold tailWord_3866297
  simp only [CollatzResearch.WordTrace]
  refine ⟨141015436474073754802669145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94010290982715836535112763 141015436474073754802669145)
  ·
    refine ⟨105761577355555316102001859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141015436474073754802669145 105761577355555316102001859)
    ·
      refine ⟨158642366033332974153002789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105761577355555316102001859 158642366033332974153002789)
      ·
        refine ⟨29745443631249932653688023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158642366033332974153002789 29745443631249932653688023)
        ·
          refine ⟨44618165446874898980532035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29745443631249932653688023 44618165446874898980532035)
          ·
            refine ⟨66927248170312348470798053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44618165446874898980532035 66927248170312348470798053)
            ·
              refine ⟨12548859031933565338274635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66927248170312348470798053 12548859031933565338274635)
              ·
                refine ⟨18823288547900348007411953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12548859031933565338274635 18823288547900348007411953)
                ·
                  refine ⟨14117466410925261005558965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18823288547900348007411953 14117466410925261005558965)
                  ·
                    refine ⟨1323512476024243219271153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14117466410925261005558965 1323512476024243219271153)
                    ·
                      rfl

theorem cell22_3866297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_3866297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866297 prefixEnd_3866297 := by exact prefixLift 3866297
  have htrace : WordTrace (prefixWord ++ tailWord_3866297) baseStart_3866297 baseEnd_3866297 := by
    simpa [prefixWord, tailWord_3866297, baseEnd_3866297] using wordTrace_append hprefix tailTrace_3866297
  have hstable : (prefixWord ++ tailWord_3866297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866297).length < 2 ^ (prefixWord ++ tailWord_3866297).sum := by decide
  have hdescent : baseEnd_3866297 < baseStart_3866297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866329 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_3866329 : Nat := 118140960795 + 3866329 * 2 ^ 59
def prefixEnd_3866329 : Nat := 4983230072969 + 3 ^ 40 * 3866329 * 2
def baseEnd_3866329 : Nat := 1323523430278205802471055

theorem tailTrace_3866329 : CollatzResearch.WordTrace tailWord_3866329 prefixEnd_3866329 1323523430278205802471055 := by
  unfold tailWord_3866329
  simp only [CollatzResearch.WordTrace]
  refine ⟨141016603609957824267834041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94011069073305216178556027 141016603609957824267834041)
  ·
    refine ⟨105762452707468368200875531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141016603609957824267834041 105762452707468368200875531)
    ·
      refine ⟨158643679061202552301313297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105762452707468368200875531 158643679061202552301313297)
      ·
        refine ⟨118982759295901914225984973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158643679061202552301313297 118982759295901914225984973)
        ·
          refine ⟨44618534735963217834744365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118982759295901914225984973 44618534735963217834744365)
          ·
            refine ⟨16731950525986206688029137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44618534735963217834744365 16731950525986206688029137)
            ·
              refine ⟨12548962894489655016021853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16731950525986206688029137 12548962894489655016021853)
              ·
                refine ⟨4705861085433620631008195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12548962894489655016021853 4705861085433620631008195)
                ·
                  refine ⟨7058791628150430946512293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705861085433620631008195 7058791628150430946512293)
                  ·
                    refine ⟨1323523430278205802471055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058791628150430946512293 1323523430278205802471055)
                    ·
                      rfl

theorem cell22_3866329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_3866329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866329 prefixEnd_3866329 := by exact prefixLift 3866329
  have htrace : WordTrace (prefixWord ++ tailWord_3866329) baseStart_3866329 baseEnd_3866329 := by
    simpa [prefixWord, tailWord_3866329, baseEnd_3866329] using wordTrace_append hprefix tailTrace_3866329
  have hstable : (prefixWord ++ tailWord_3866329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866329).length < 2 ^ (prefixWord ++ tailWord_3866329).sum := by decide
  have hdescent : baseEnd_3866329 < baseStart_3866329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866344 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_3866344 : Nat := 118140960795 + 3866344 * 2 ^ 59
def prefixEnd_3866344 : Nat := 4983230072969 + 3 ^ 40 * 3866344 * 2
def baseEnd_3866344 : Nat := 441176188361583587782003

theorem tailTrace_3866344 : CollatzResearch.WordTrace tailWord_3866344 prefixEnd_3866344 441176188361583587782003 := by
  unfold tailWord_3866344
  simp only [CollatzResearch.WordTrace]
  refine ⟨70508575352451740914815043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94011433803268987886420057 70508575352451740914815043)
  ·
    refine ⟨105762863028677611372222565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70508575352451740914815043 105762863028677611372222565)
    ·
      refine ⟨19830536817877052132291731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105762863028677611372222565 19830536817877052132291731)
      ·
        refine ⟨29745805226815578198437597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19830536817877052132291731 29745805226815578198437597)
        ·
          refine ⟨11154676960055841824414099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29745805226815578198437597 11154676960055841824414099)
          ·
            refine ⟨16732015440083762736621149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154676960055841824414099 16732015440083762736621149)
            ·
              refine ⟨6274505790031411026232931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16732015440083762736621149 6274505790031411026232931)
              ·
                refine ⟨9411758685047116539349397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274505790031411026232931 9411758685047116539349397)
                ·
                  refine ⟨441176188361583587782003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9411758685047116539349397 441176188361583587782003)
                  ·
                    rfl

theorem cell22_3866344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_3866344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866344 prefixEnd_3866344 := by exact prefixLift 3866344
  have htrace : WordTrace (prefixWord ++ tailWord_3866344) baseStart_3866344 baseEnd_3866344 := by
    simpa [prefixWord, tailWord_3866344, baseEnd_3866344] using wordTrace_append hprefix tailTrace_3866344
  have hstable : (prefixWord ++ tailWord_3866344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866344).length < 2 ^ (prefixWord ++ tailWord_3866344).sum := by decide
  have hdescent : baseEnd_3866344 < baseStart_3866344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866425 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 2, 4]
def baseStart_3866425 : Nat := 118140960795 + 3866425 * 2 ^ 59
def prefixEnd_3866425 : Nat := 4983230072969 + 3 ^ 40 * 3866425 * 2
def baseEnd_3866425 : Nat := 1323556293040093552070761

theorem tailTrace_3866425 : CollatzResearch.WordTrace tailWord_3866425 prefixEnd_3866425 1323556293040093552070761 := by
  unfold tailWord_3866425
  simp only [CollatzResearch.WordTrace]
  refine ⟨141020105017610032663328729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94013403345073355108885819 141020105017610032663328729)
  ·
    refine ⟨105765078763207524497496547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141020105017610032663328729 105765078763207524497496547)
    ·
      refine ⟨158647618144811286746244821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105765078763207524497496547 158647618144811286746244821)
      ·
        refine ⟨3718303550269014533115113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 158647618144811286746244821 3718303550269014533115113)
        ·
          refine ⟨2788727662701760899836335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3718303550269014533115113 2788727662701760899836335)
          ·
            refine ⟨4183091494052641349754503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788727662701760899836335 4183091494052641349754503)
            ·
              refine ⟨6274637241078962024631755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183091494052641349754503 6274637241078962024631755)
              ·
                refine ⟨9411955861618443036947633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274637241078962024631755 9411955861618443036947633)
                ·
                  refine ⟨7058966896213832277710725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411955861618443036947633 7058966896213832277710725)
                  ·
                    refine ⟨1323556293040093552070761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058966896213832277710725 1323556293040093552070761)
                    ·
                      rfl

theorem cell22_3866425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_3866425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866425 prefixEnd_3866425 := by exact prefixLift 3866425
  have htrace : WordTrace (prefixWord ++ tailWord_3866425) baseStart_3866425 baseEnd_3866425 := by
    simpa [prefixWord, tailWord_3866425, baseEnd_3866425] using wordTrace_append hprefix tailTrace_3866425
  have hstable : (prefixWord ++ tailWord_3866425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866425).length < 2 ^ (prefixWord ++ tailWord_3866425).sum := by decide
  have hdescent : baseEnd_3866425 < baseStart_3866425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866449 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_3866449 : Nat := 118140960795 + 3866449 * 2 ^ 59
def prefixEnd_3866449 : Nat := 4983230072969 + 3 ^ 40 * 3866449 * 2
def baseEnd_3866449 : Nat := 1323564508730565489470687

theorem tailTrace_3866449 : CollatzResearch.WordTrace tailWord_3866449 prefixEnd_3866449 1323564508730565489470687 := by
  unfold tailWord_3866449
  simp only [CollatzResearch.WordTrace]
  refine ⟨141020980369523084762202401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94013986913015389841468267 141020980369523084762202401)
  ·
    refine ⟨105765735277142313571651801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141020980369523084762202401 105765735277142313571651801)
    ·
      refine ⟨79324301457856735178738851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105765735277142313571651801 79324301457856735178738851)
      ·
        refine ⟨118986452186785102768108277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79324301457856735178738851 118986452186785102768108277)
        ·
          refine ⟨11154979892511103384510151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118986452186785102768108277 11154979892511103384510151)
          ·
            refine ⟨16732469838766655076765227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154979892511103384510151 16732469838766655076765227)
            ·
              refine ⟨25098704758149982615147841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16732469838766655076765227 25098704758149982615147841)
              ·
                refine ⟨18824028568612486961360881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25098704758149982615147841 18824028568612486961360881)
                ·
                  refine ⟨14118021426459365221020661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18824028568612486961360881 14118021426459365221020661)
                  ·
                    refine ⟨1323564508730565489470687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14118021426459365221020661 1323564508730565489470687)
                    ·
                      rfl

theorem cell22_3866449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_3866449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866449 prefixEnd_3866449 := by exact prefixLift 3866449
  have htrace : WordTrace (prefixWord ++ tailWord_3866449) baseStart_3866449 baseEnd_3866449 := by
    simpa [prefixWord, tailWord_3866449, baseEnd_3866449] using wordTrace_append hprefix tailTrace_3866449
  have hstable : (prefixWord ++ tailWord_3866449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866449).length < 2 ^ (prefixWord ++ tailWord_3866449).sum := by decide
  have hdescent : baseEnd_3866449 < baseStart_3866449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866466 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3866466 : Nat := 118140960795 + 3866466 * 2 ^ 59
def prefixEnd_3866466 : Nat := 4983230072969 + 3 ^ 40 * 3866466 * 2
def baseEnd_3866466 : Nat := 1323570328177983111795635

theorem tailTrace_3866466 : CollatzResearch.WordTrace tailWord_3866466 prefixEnd_3866466 1323570328177983111795635 := by
  unfold tailWord_3866466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35255400102615374166392813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94014400273640997777047501 35255400102615374166392813)
  ·
    refine ⟨13220775038480765312397305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35255400102615374166392813 13220775038480765312397305)
    ·
      refine ⟨9915581278860573984297979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13220775038480765312397305 9915581278860573984297979)
      ·
        refine ⟨14873371918290860976446969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9915581278860573984297979 14873371918290860976446969)
        ·
          refine ⟨11155028938718145732335227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14873371918290860976446969 11155028938718145732335227)
          ·
            refine ⟨16732543408077218598502841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11155028938718145732335227 16732543408077218598502841)
            ·
              refine ⟨12549407556057913948877131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16732543408077218598502841 12549407556057913948877131)
              ·
                refine ⟨18824111334086870923315697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12549407556057913948877131 18824111334086870923315697)
                ·
                  refine ⟨14118083500565153192486773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18824111334086870923315697 14118083500565153192486773)
                  ·
                    refine ⟨1323570328177983111795635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14118083500565153192486773 1323570328177983111795635)
                    ·
                      rfl

theorem cell22_3866466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3866466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866466 prefixEnd_3866466 := by exact prefixLift 3866466
  have htrace : WordTrace (prefixWord ++ tailWord_3866466) baseStart_3866466 baseEnd_3866466 := by
    simpa [prefixWord, tailWord_3866466, baseEnd_3866466] using wordTrace_append hprefix tailTrace_3866466
  have hstable : (prefixWord ++ tailWord_3866466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866466).length < 2 ^ (prefixWord ++ tailWord_3866466).sum := by decide
  have hdescent : baseEnd_3866466 < baseStart_3866466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866468 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 5]
def baseStart_3866468 : Nat := 118140960795 + 3866468 * 2 ^ 59
def prefixEnd_3866468 : Nat := 4983230072969 + 3 ^ 40 * 3866468 * 2
def baseEnd_3866468 : Nat := 441190337606285257748543

theorem tailTrace_3866468 : CollatzResearch.WordTrace tailWord_3866468 prefixEnd_3866468 441190337606285257748543 := by
  unfold tailWord_3866468
  simp only [CollatzResearch.WordTrace]
  refine ⟨70510836678227125503572029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94014448904302834004762705 70510836678227125503572029)
  ·
    refine ⟨26441563754335172063839511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70510836678227125503572029 26441563754335172063839511)
    ·
      refine ⟨39662345631502758095759267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26441563754335172063839511 39662345631502758095759267)
      ·
        refine ⟨59493518447254137143638901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39662345631502758095759267 59493518447254137143638901)
        ·
          refine ⟨5577517354430075357216147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59493518447254137143638901 5577517354430075357216147)
          ·
            refine ⟨8366276031645113035824221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577517354430075357216147 8366276031645113035824221)
            ·
              refine ⟨3137353511866917388434083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8366276031645113035824221 3137353511866917388434083)
              ·
                refine ⟨4706030267800376082651125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137353511866917388434083 4706030267800376082651125)
                ·
                  refine ⟨441190337606285257748543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706030267800376082651125 441190337606285257748543)
                  ·
                    rfl

theorem cell22_3866468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_3866468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866468 prefixEnd_3866468 := by exact prefixLift 3866468
  have htrace : WordTrace (prefixWord ++ tailWord_3866468) baseStart_3866468 baseEnd_3866468 := by
    simpa [prefixWord, tailWord_3866468, baseEnd_3866468] using wordTrace_append hprefix tailTrace_3866468
  have hstable : (prefixWord ++ tailWord_3866468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866468).length < 2 ^ (prefixWord ++ tailWord_3866468).sum := by decide
  have hdescent : baseEnd_3866468 < baseStart_3866468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866481 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_3866481 : Nat := 118140960795 + 3866481 * 2 ^ 59
def prefixEnd_3866481 : Nat := 4983230072969 + 3 ^ 40 * 3866481 * 2
def baseEnd_3866481 : Nat := 1323575462984528072670589

theorem tailTrace_3866481 : CollatzResearch.WordTrace tailWord_3866481 prefixEnd_3866481 1323575462984528072670589 := by
  unfold tailWord_3866481
  simp only [CollatzResearch.WordTrace]
  refine ⟨141022147505407154227367297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94014765003604769484911531 141022147505407154227367297)
  ·
    refine ⟨105766610629055365670525473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141022147505407154227367297 105766610629055365670525473)
    ·
      refine ⟨79324957971791524252894105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105766610629055365670525473 79324957971791524252894105)
      ·
        refine ⟨59493718478843643189670579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79324957971791524252894105 59493718478843643189670579)
        ·
          refine ⟨89240577718265464784505869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59493718478843643189670579 89240577718265464784505869)
          ·
            refine ⟨33465216644349549294189701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89240577718265464784505869 33465216644349549294189701)
            ·
              refine ⟨6274728120815540492660569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33465216644349549294189701 6274728120815540492660569)
              ·
                refine ⟨4706046090611655369495427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6274728120815540492660569 4706046090611655369495427)
                ·
                  refine ⟨7059069135917483054243141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706046090611655369495427 7059069135917483054243141)
                  ·
                    refine ⟨1323575462984528072670589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7059069135917483054243141 1323575462984528072670589)
                    ·
                      rfl

theorem cell22_3866481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_3866481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866481 prefixEnd_3866481 := by exact prefixLift 3866481
  have htrace : WordTrace (prefixWord ++ tailWord_3866481) baseStart_3866481 baseEnd_3866481 := by
    simpa [prefixWord, tailWord_3866481, baseEnd_3866481] using wordTrace_append hprefix tailTrace_3866481
  have hstable : (prefixWord ++ tailWord_3866481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866481).length < 2 ^ (prefixWord ++ tailWord_3866481).sum := by decide
  have hdescent : baseEnd_3866481 < baseStart_3866481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866631 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 6]
def baseStart_3866631 : Nat := 118140960795 + 3866631 * 2 ^ 59
def prefixEnd_3866631 : Nat := 4983230072969 + 3 ^ 40 * 3866631 * 2
def baseEnd_3866631 : Nat := 441208937016659227140043

theorem tailTrace_3866631 : CollatzResearch.WordTrace tailWord_3866631 prefixEnd_3866631 441208937016659227140043 := by
  unfold tailWord_3866631
  simp only [CollatzResearch.WordTrace]
  refine ⟨141027618454863729845327747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94018412303242486563551831 141027618454863729845327747)
  ·
    refine ⟨211541427682295594767991621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141027618454863729845327747 211541427682295594767991621)
    ·
      refine ⟨39664017690430424018998429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211541427682295594767991621 39664017690430424018998429)
      ·
        refine ⟨14874006633911409007124411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39664017690430424018998429 14874006633911409007124411)
        ·
          refine ⟨22311009950867113510686617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874006633911409007124411 22311009950867113510686617)
          ·
            refine ⟨16733257463150335133014963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22311009950867113510686617 16733257463150335133014963)
            ·
              refine ⟨25099886194725502699522445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16733257463150335133014963 25099886194725502699522445)
              ·
                refine ⟨9412457323022063512320917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25099886194725502699522445 9412457323022063512320917)
                ·
                  refine ⟨441208937016659227140043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9412457323022063512320917 441208937016659227140043)
                  ·
                    rfl

theorem cell22_3866631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 6].length) (baseStart_3866631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866631 prefixEnd_3866631 := by exact prefixLift 3866631
  have htrace : WordTrace (prefixWord ++ tailWord_3866631) baseStart_3866631 baseEnd_3866631 := by
    simpa [prefixWord, tailWord_3866631, baseEnd_3866631] using wordTrace_append hprefix tailTrace_3866631
  have hstable : (prefixWord ++ tailWord_3866631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866631).length < 2 ^ (prefixWord ++ tailWord_3866631).sum := by decide
  have hdescent : baseEnd_3866631 < baseStart_3866631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866661 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3866661 : Nat := 118140960795 + 3866661 * 2 ^ 59
def prefixEnd_3866661 : Nat := 4983230072969 + 3 ^ 40 * 3866661 * 2
def baseEnd_3866661 : Nat := 1323637080663067603170037

theorem tailTrace_3866661 : CollatzResearch.WordTrace tailWord_3866661 prefixEnd_3866661 1323637080663067603170037 := by
  unfold tailWord_3866661
  simp only [CollatzResearch.WordTrace]
  refine ⟨141028712644755044968919837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94019141763170029979279891 141028712644755044968919837)
  ·
    refine ⟨52885767241783141863344939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141028712644755044968919837 52885767241783141863344939)
    ·
      refine ⟨79328650862674712795017409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52885767241783141863344939 79328650862674712795017409)
      ·
        refine ⟨59496488147006034596263057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79328650862674712795017409 59496488147006034596263057)
        ·
          refine ⟨44622366110254525947197293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59496488147006034596263057 44622366110254525947197293)
          ·
            refine ⟨16733387291345447230198985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44622366110254525947197293 16733387291345447230198985)
            ·
              refine ⟨12550040468509085422649239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16733387291345447230198985 12550040468509085422649239)
              ·
                refine ⟨18825060702763628133973859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12550040468509085422649239 18825060702763628133973859)
                ·
                  refine ⟨28237591054145442200960789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18825060702763628133973859 28237591054145442200960789)
                  ·
                    refine ⟨1323637080663067603170037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28237591054145442200960789 1323637080663067603170037)
                    ·
                      rfl

theorem cell22_3866661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3866661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866661 prefixEnd_3866661 := by exact prefixLift 3866661
  have htrace : WordTrace (prefixWord ++ tailWord_3866661) baseStart_3866661 baseEnd_3866661 := by
    simpa [prefixWord, tailWord_3866661, baseEnd_3866661] using wordTrace_append hprefix tailTrace_3866661
  have hstable : (prefixWord ++ tailWord_3866661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866661).length < 2 ^ (prefixWord ++ tailWord_3866661).sum := by decide
  have hdescent : baseEnd_3866661 < baseStart_3866661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866708 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3866708 : Nat := 118140960795 + 3866708 * 2 ^ 59
def prefixEnd_3866708 : Nat := 4983230072969 + 3 ^ 40 * 3866708 * 2
def baseEnd_3866708 : Nat := 1323653169723575147244893

theorem tailTrace_3866708 : CollatzResearch.WordTrace tailWord_3866708 prefixEnd_3866708 1323653169723575147244893 := by
  unfold tailWord_3866708
  simp only [CollatzResearch.WordTrace]
  refine ⟨70515213437792385997940389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94020284583723181330587185 70515213437792385997940389)
  ·
    refine ⟨13221602519586072374613823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70515213437792385997940389 13221602519586072374613823)
    ·
      refine ⟨19832403779379108561920735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13221602519586072374613823 19832403779379108561920735)
      ·
        refine ⟨29748605669068662842881103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19832403779379108561920735 29748605669068662842881103)
        ·
          refine ⟨44622908503602994264321655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29748605669068662842881103 44622908503602994264321655)
          ·
            refine ⟨66934362755404491396482483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44622908503602994264321655 66934362755404491396482483)
            ·
              refine ⟨100401544133106737094723725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66934362755404491396482483 100401544133106737094723725)
              ·
                refine ⟨37650579049915026410521397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100401544133106737094723725 37650579049915026410521397)
                ·
                  refine ⟨3529741785929533725986381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37650579049915026410521397 3529741785929533725986381)
                  ·
                    refine ⟨1323653169723575147244893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529741785929533725986381 1323653169723575147244893)
                    ·
                      rfl

theorem cell22_3866708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3866708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866708 prefixEnd_3866708 := by exact prefixLift 3866708
  have htrace : WordTrace (prefixWord ++ tailWord_3866708) baseStart_3866708 baseEnd_3866708 := by
    simpa [prefixWord, tailWord_3866708, baseEnd_3866708] using wordTrace_append hprefix tailTrace_3866708
  have hstable : (prefixWord ++ tailWord_3866708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866708).length < 2 ^ (prefixWord ++ tailWord_3866708).sum := by decide
  have hdescent : baseEnd_3866708 < baseStart_3866708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866710 : List Nat := [5, 2, 2, 1, 1, 1, 2, 8]
def baseStart_3866710 : Nat := 118140960795 + 3866710 * 2 ^ 59
def prefixEnd_3866710 : Nat := 4983230072969 + 3 ^ 40 * 3866710 * 2
def baseEnd_3866710 : Nat := 147072650484938645410543

theorem tailTrace_3866710 : CollatzResearch.WordTrace tailWord_3866710 prefixEnd_3866710 147072650484938645410543 := by
  unfold tailWord_3866710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814406238848595396090849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94020333214385017558302389 8814406238848595396090849)
  ·
    refine ⟨6610804679136446547068137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8814406238848595396090849 6610804679136446547068137)
    ·
      refine ⟨4958103509352334910301103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6610804679136446547068137 4958103509352334910301103)
      ·
        refine ⟨7437155264028502365451655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958103509352334910301103 7437155264028502365451655)
        ·
          refine ⟨11155732896042753548177483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437155264028502365451655 11155732896042753548177483)
          ·
            refine ⟨16733599344064130322266225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11155732896042753548177483 16733599344064130322266225)
            ·
              refine ⟨12550199508048097741699669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16733599344064130322266225 12550199508048097741699669)
              ·
                refine ⟨147072650484938645410543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12550199508048097741699669 147072650484938645410543)
                ·
                  rfl

theorem cell22_3866710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_3866710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866710 prefixEnd_3866710 := by exact prefixLift 3866710
  have htrace : WordTrace (prefixWord ++ tailWord_3866710) baseStart_3866710 baseEnd_3866710 := by
    simpa [prefixWord, tailWord_3866710, baseEnd_3866710] using wordTrace_append hprefix tailTrace_3866710
  have hstable : (prefixWord ++ tailWord_3866710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866710).length < 2 ^ (prefixWord ++ tailWord_3866710).sum := by decide
  have hdescent : baseEnd_3866710 < baseStart_3866710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866738 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_3866738 : Nat := 118140960795 + 3866738 * 2 ^ 59
def prefixEnd_3866738 : Nat := 4983230072969 + 3 ^ 40 * 3866738 * 2
def baseEnd_3866738 : Nat := 441221146445555022998267

theorem tailTrace_3866738 : CollatzResearch.WordTrace tailWord_3866738 prefixEnd_3866738 441221146445555022998267 := by
  unfold tailWord_3866738
  simp only [CollatzResearch.WordTrace]
  refine ⟨35257880266369021779868217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94021014043650724746315245 35257880266369021779868217)
  ·
    refine ⟨26443410199776766334901163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35257880266369021779868217 26443410199776766334901163)
    ·
      refine ⟨39665115299665149502351745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26443410199776766334901163 39665115299665149502351745)
      ·
        refine ⟨29748836474748862126763809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39665115299665149502351745 29748836474748862126763809)
        ·
          refine ⟨22311627356061646595072857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29748836474748862126763809 22311627356061646595072857)
          ·
            refine ⟨16733720517046234946304643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22311627356061646595072857 16733720517046234946304643)
            ·
              refine ⟨25100580775569352419456965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16733720517046234946304643 25100580775569352419456965)
              ·
                refine ⟨4706358895419253578648181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25100580775569352419456965 4706358895419253578648181)
                ·
                  refine ⟨441221146445555022998267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706358895419253578648181 441221146445555022998267)
                  ·
                    rfl

theorem cell22_3866738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_3866738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866738 prefixEnd_3866738 := by exact prefixLift 3866738
  have htrace : WordTrace (prefixWord ++ tailWord_3866738) baseStart_3866738 baseEnd_3866738 := by
    simpa [prefixWord, tailWord_3866738, baseEnd_3866738] using wordTrace_append hprefix tailTrace_3866738
  have hstable : (prefixWord ++ tailWord_3866738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866738).length < 2 ^ (prefixWord ++ tailWord_3866738).sum := by decide
  have hdescent : baseEnd_3866738 < baseStart_3866738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866768 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_3866768 : Nat := 118140960795 + 3866768 * 2 ^ 59
def prefixEnd_3866768 : Nat := 4983230072969 + 3 ^ 40 * 3866768 * 2
def baseEnd_3866768 : Nat := 1323673708949754990744709

theorem tailTrace_3866768 : CollatzResearch.WordTrace tailWord_3866768 prefixEnd_3866768 1323673708949754990744709 := by
  unfold tailWord_3866768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70516307627683701121532479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94021743503578268162043305 70516307627683701121532479)
  ·
    refine ⟨105774461441525551682298719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70516307627683701121532479 105774461441525551682298719)
    ·
      refine ⟨158661692162288327523448079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105774461441525551682298719 158661692162288327523448079)
      ·
        refine ⟨237992538243432491285172119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158661692162288327523448079 237992538243432491285172119)
        ·
          refine ⟨356988807365148736927758179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237992538243432491285172119 356988807365148736927758179)
          ·
            refine ⟨535483211047723105391637269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356988807365148736927758179 535483211047723105391637269)
            ·
              refine ⟨25100775517862020565232997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535483211047723105391637269 25100775517862020565232997)
              ·
                refine ⟨4706395409599128855981187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25100775517862020565232997 4706395409599128855981187)
                ·
                  refine ⟨7059593114398693283971781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706395409599128855981187 7059593114398693283971781)
                  ·
                    refine ⟨1323673708949754990744709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7059593114398693283971781 1323673708949754990744709)
                    ·
                      rfl

theorem cell22_3866768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_3866768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866768 prefixEnd_3866768 := by exact prefixLift 3866768
  have htrace : WordTrace (prefixWord ++ tailWord_3866768) baseStart_3866768 baseEnd_3866768 := by
    simpa [prefixWord, tailWord_3866768, baseEnd_3866768] using wordTrace_append hprefix tailTrace_3866768
  have hstable : (prefixWord ++ tailWord_3866768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866768).length < 2 ^ (prefixWord ++ tailWord_3866768).sum := by decide
  have hdescent : baseEnd_3866768 < baseStart_3866768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866785 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3866785 : Nat := 118140960795 + 3866785 * 2 ^ 59
def prefixEnd_3866785 : Nat := 4983230072969 + 3 ^ 40 * 3866785 * 2
def baseEnd_3866785 : Nat := 1323679528397172613069657

theorem tailTrace_3866785 : CollatzResearch.WordTrace tailWord_3866785 prefixEnd_3866785 1323679528397172613069657 := by
  unfold tailWord_3866785
  simp only [CollatzResearch.WordTrace]
  refine ⟨141033235296305814146433809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94022156864203876097622539 141033235296305814146433809)
  ·
    refine ⟨105774926472229360609825357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141033235296305814146433809 105774926472229360609825357)
    ·
      refine ⟨39665597427086010228684509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105774926472229360609825357 39665597427086010228684509)
      ·
        refine ⟨14874599035157253835756691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39665597427086010228684509 14874599035157253835756691)
        ·
          refine ⟨22311898552735880753635037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874599035157253835756691 22311898552735880753635037)
          ·
            refine ⟨8366961957275955282613139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22311898552735880753635037 8366961957275955282613139)
            ·
              refine ⟨12550442935913932923919709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8366961957275955282613139 12550442935913932923919709)
              ·
                refine ⟨4706416100967724846469891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12550442935913932923919709 4706416100967724846469891)
                ·
                  refine ⟨7059624151451587269704837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706416100967724846469891 7059624151451587269704837)
                  ·
                    refine ⟨1323679528397172613069657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7059624151451587269704837 1323679528397172613069657)
                    ·
                      rfl

theorem cell22_3866785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3866785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866785 prefixEnd_3866785 := by exact prefixLift 3866785
  have htrace : WordTrace (prefixWord ++ tailWord_3866785) baseStart_3866785 baseEnd_3866785 := by
    simpa [prefixWord, tailWord_3866785, baseEnd_3866785] using wordTrace_append hprefix tailTrace_3866785
  have hstable : (prefixWord ++ tailWord_3866785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866785).length < 2 ^ (prefixWord ++ tailWord_3866785).sum := by decide
  have hdescent : baseEnd_3866785 < baseStart_3866785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866811 : List Nat := [1, 1, 1, 1, 1, 2, 6, 9]
def baseStart_3866811 : Nat := 118140960795 + 3866811 * 2 ^ 59
def prefixEnd_3866811 : Nat := 4983230072969 + 3 ^ 40 * 3866811 * 2
def baseEnd_3866811 : Nat := 147076492080946356879953

theorem tailTrace_3866811 : CollatzResearch.WordTrace tailWord_3866811 prefixEnd_3866811 147076492080946356879953 := by
  unfold tailWord_3866811
  simp only [CollatzResearch.WordTrace]
  refine ⟨141034183594211620586880287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94022789062807747057920191 141034183594211620586880287)
  ·
    refine ⟨211551275391317430880320431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141034183594211620586880287 211551275391317430880320431)
    ·
      refine ⟨317326913086976146320480647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211551275391317430880320431 317326913086976146320480647)
      ·
        refine ⟨475990369630464219480720971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317326913086976146320480647 475990369630464219480720971)
        ·
          refine ⟨713985554445696329221081457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475990369630464219480720971 713985554445696329221081457)
          ·
            refine ⟨535489165834272246915811093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713985554445696329221081457 535489165834272246915811093)
            ·
              refine ⟨25101054648481511574178645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535489165834272246915811093 25101054648481511574178645)
              ·
                refine ⟨147076492080946356879953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25101054648481511574178645 147076492080946356879953)
                ·
                  rfl

theorem cell22_3866811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 9].length) (baseStart_3866811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866811 prefixEnd_3866811 := by exact prefixLift 3866811
  have htrace : WordTrace (prefixWord ++ tailWord_3866811) baseStart_3866811 baseEnd_3866811 := by
    simpa [prefixWord, tailWord_3866811, baseEnd_3866811] using wordTrace_append hprefix tailTrace_3866811
  have hstable : (prefixWord ++ tailWord_3866811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866811).length < 2 ^ (prefixWord ++ tailWord_3866811).sum := by decide
  have hdescent : baseEnd_3866811 < baseStart_3866811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866843 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 7, 3]
def baseStart_3866843 : Nat := 118140960795 + 3866843 * 2 ^ 59
def prefixEnd_3866843 : Nat := 4983230072969 + 3 ^ 40 * 3866843 * 2
def baseEnd_3866843 : Nat := 1323699382982479795119479

theorem tailTrace_3866843 : CollatzResearch.WordTrace tailWord_3866843 prefixEnd_3866843 1323699382982479795119479 := by
  unfold tailWord_3866843
  simp only [CollatzResearch.WordTrace]
  refine ⟨141035350730095690052045183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94023567153397126701363455 141035350730095690052045183)
  ·
    refine ⟨211553026095143535078067775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141035350730095690052045183 211553026095143535078067775)
    ·
      refine ⟨317329539142715302617101663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211553026095143535078067775 317329539142715302617101663)
      ·
        refine ⟨475994308714072953925652495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317329539142715302617101663 475994308714072953925652495)
        ·
          refine ⟨713991463071109430888478743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475994308714072953925652495 713991463071109430888478743)
          ·
            refine ⟨1070987194606664146332718115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713991463071109430888478743 1070987194606664146332718115)
            ·
              refine ⟨1606480791909996219499077173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070987194606664146332718115 1606480791909996219499077173)
              ·
                refine ⟨150607574241562145578038485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1606480791909996219499077173 150607574241562145578038485)
                ·
                  refine ⟨3529865021286612786985277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 150607574241562145578038485 3529865021286612786985277)
                  ·
                    refine ⟨1323699382982479795119479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529865021286612786985277 1323699382982479795119479)
                    ·
                      rfl

theorem cell22_3866843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 3].length) (baseStart_3866843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866843 prefixEnd_3866843 := by exact prefixLift 3866843
  have htrace : WordTrace (prefixWord ++ tailWord_3866843) baseStart_3866843 baseEnd_3866843 := by
    simpa [prefixWord, tailWord_3866843, baseEnd_3866843] using wordTrace_append hprefix tailTrace_3866843
  have hstable : (prefixWord ++ tailWord_3866843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866843).length < 2 ^ (prefixWord ++ tailWord_3866843).sum := by decide
  have hdescent : baseEnd_3866843 < baseStart_3866843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866845 : List Nat := [1, 4, 3, 2, 1, 3, 8]
def baseStart_3866845 : Nat := 118140960795 + 3866845 * 2 ^ 59
def prefixEnd_3866845 : Nat := 4983230072969 + 3 ^ 40 * 3866845 * 2
def baseEnd_3866845 : Nat := 49025928430494535428499

theorem tailTrace_3866845 : CollatzResearch.WordTrace tailWord_3866845 prefixEnd_3866845 49025928430494535428499 := by
  unfold tailWord_3866845
  simp only [CollatzResearch.WordTrace]
  refine ⟨141035423676088444393617989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94023615784058962929078659 141035423676088444393617989)
  ·
    refine ⟨26444141939266583323803373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141035423676088444393617989 26444141939266583323803373)
    ·
      refine ⟨9916553227224968746426265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26444141939266583323803373 9916553227224968746426265)
      ·
        refine ⟨7437414920418726559819699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9916553227224968746426265 7437414920418726559819699)
        ·
          refine ⟨11156122380628089839729549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437414920418726559819699 11156122380628089839729549)
          ·
            refine ⟨4183545892735533689898581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11156122380628089839729549 4183545892735533689898581)
            ·
              refine ⟨49025928430494535428499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4183545892735533689898581 49025928430494535428499)
              ·
                rfl

theorem cell22_3866845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 8].length) (baseStart_3866845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866845 prefixEnd_3866845 := by exact prefixLift 3866845
  have htrace : WordTrace (prefixWord ++ tailWord_3866845) baseStart_3866845 baseEnd_3866845 := by
    simpa [prefixWord, tailWord_3866845, baseEnd_3866845] using wordTrace_append hprefix tailTrace_3866845
  have hstable : (prefixWord ++ tailWord_3866845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866845).length < 2 ^ (prefixWord ++ tailWord_3866845).sum := by decide
  have hdescent : baseEnd_3866845 < baseStart_3866845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866858 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3866858 : Nat := 118140960795 + 3866858 * 2 ^ 59
def prefixEnd_3866858 : Nat := 4983230072969 + 3 ^ 40 * 3866858 * 2
def baseEnd_3866858 : Nat := 1323704517789024755994433

theorem tailTrace_3866858 : CollatzResearch.WordTrace tailWord_3866858 prefixEnd_3866858 1323704517789024755994433 := by
  unfold tailWord_3866858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35258974456260336903460307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94023931883360898409227485 35258974456260336903460307)
  ·
    refine ⟨52888461684390505355190461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35258974456260336903460307 52888461684390505355190461)
    ·
      refine ⟨19833173131646439508196423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52888461684390505355190461 19833173131646439508196423)
      ·
        refine ⟨29749759697469659262294635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19833173131646439508196423 29749759697469659262294635)
        ·
          refine ⟨44624639546204488893441953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29749759697469659262294635 44624639546204488893441953)
          ·
            refine ⟨33468479659653366670081465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44624639546204488893441953 33468479659653366670081465)
            ·
              refine ⟨25101359744740025002561099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33468479659653366670081465 25101359744740025002561099)
              ·
                refine ⟨37652039617110037503841649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25101359744740025002561099 37652039617110037503841649)
                ·
                  refine ⟨28239029712832528127881237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37652039617110037503841649 28239029712832528127881237)
                  ·
                    refine ⟨1323704517789024755994433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28239029712832528127881237 1323704517789024755994433)
                    ·
                      rfl

theorem cell22_3866858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3866858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866858 prefixEnd_3866858 := by exact prefixLift 3866858
  have htrace : WordTrace (prefixWord ++ tailWord_3866858) baseStart_3866858 baseEnd_3866858 := by
    simpa [prefixWord, tailWord_3866858, baseEnd_3866858] using wordTrace_append hprefix tailTrace_3866858
  have hstable : (prefixWord ++ tailWord_3866858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866858).length < 2 ^ (prefixWord ++ tailWord_3866858).sum := by decide
  have hdescent : baseEnd_3866858 < baseStart_3866858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866911 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 1, 3]
def baseStart_3866911 : Nat := 118140960795 + 3866911 * 2 ^ 59
def prefixEnd_3866911 : Nat := 4983230072969 + 3 ^ 40 * 3866911 * 2
def baseEnd_3866911 : Nat := 1323722660772150284419271

theorem tailTrace_3866911 : CollatzResearch.WordTrace tailWord_3866911 prefixEnd_3866911 1323722660772150284419271 := by
  unfold tailWord_3866911
  simp only [CollatzResearch.WordTrace]
  refine ⟨141037830893849337665520587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94025220595899558443680391 141037830893849337665520587)
  ·
    refine ⟨211556746340774006498280881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141037830893849337665520587 211556746340774006498280881)
    ·
      refine ⟨158667559755580504873710661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211556746340774006498280881 158667559755580504873710661)
      ·
        refine ⟨29750167454171344663820749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158667559755580504873710661 29750167454171344663820749)
        ·
          refine ⟨11156312795314254248932781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29750167454171344663820749 11156312795314254248932781)
          ·
            refine ⟨4183617298242845343349793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11156312795314254248932781 4183617298242845343349793)
            ·
              refine ⟨3137712973682134007512345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183617298242845343349793 3137712973682134007512345)
              ·
                refine ⟨2353284730261600505634259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137712973682134007512345 2353284730261600505634259)
                ·
                  refine ⟨3529927095392400758451389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353284730261600505634259 3529927095392400758451389)
                  ·
                    refine ⟨1323722660772150284419271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529927095392400758451389 1323722660772150284419271)
                    ·
                      rfl

theorem cell22_3866911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_3866911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866911 prefixEnd_3866911 := by exact prefixLift 3866911
  have htrace : WordTrace (prefixWord ++ tailWord_3866911) baseStart_3866911 baseEnd_3866911 := by
    simpa [prefixWord, tailWord_3866911, baseEnd_3866911] using wordTrace_append hprefix tailTrace_3866911
  have hstable : (prefixWord ++ tailWord_3866911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866911).length < 2 ^ (prefixWord ++ tailWord_3866911).sum := by decide
  have hdescent : baseEnd_3866911 < baseStart_3866911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866922 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3866922 : Nat := 118140960795 + 3866922 * 2 ^ 59
def prefixEnd_3866922 : Nat := 4983230072969 + 3 ^ 40 * 3866922 * 2
def baseEnd_3866922 : Nat := 1323726426296949922394237

theorem tailTrace_3866922 : CollatzResearch.WordTrace tailWord_3866922 prefixEnd_3866922 1323726426296949922394237 := by
  unfold tailWord_3866922
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259558024202371636042755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94025488064539657696114013 35259558024202371636042755)
  ·
    refine ⟨52889337036303557454064133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35259558024202371636042755 52889337036303557454064133)
    ·
      refine ⟨9916750694306917022637025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52889337036303557454064133 9916750694306917022637025)
      ·
        refine ⟨7437563020730187766977769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9916750694306917022637025 7437563020730187766977769)
        ·
          refine ⟨5578172265547640825233327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7437563020730187766977769 5578172265547640825233327)
          ·
            refine ⟨8367258398321461237849991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578172265547640825233327 8367258398321461237849991)
            ·
              refine ⟨12550887597482191856774987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367258398321461237849991 12550887597482191856774987)
              ·
                refine ⟨18826331396223287785162481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12550887597482191856774987 18826331396223287785162481)
                ·
                  refine ⟨14119748547167465838871861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18826331396223287785162481 14119748547167465838871861)
                  ·
                    refine ⟨1323726426296949922394237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14119748547167465838871861 1323726426296949922394237)
                    ·
                      rfl

theorem cell22_3866922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3866922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866922 prefixEnd_3866922 := by exact prefixLift 3866922
  have htrace : WordTrace (prefixWord ++ tailWord_3866922) baseStart_3866922 baseEnd_3866922 := by
    simpa [prefixWord, tailWord_3866922, baseEnd_3866922] using wordTrace_append hprefix tailTrace_3866922
  have hstable : (prefixWord ++ tailWord_3866922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866922).length < 2 ^ (prefixWord ++ tailWord_3866922).sum := by decide
  have hdescent : baseEnd_3866922 < baseStart_3866922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866997 : List Nat := [1, 3, 4, 1, 2, 1, 4, 6]
def baseStart_3866997 : Nat := 118140960795 + 3866997 * 2 ^ 59
def prefixEnd_3866997 : Nat := 4983230072969 + 3 ^ 40 * 3866997 * 2
def baseEnd_3866997 : Nat := 147083566703297191863223

theorem tailTrace_3866997 : CollatzResearch.WordTrace tailWord_3866997 prefixEnd_3866997 147083566703297191863223 := by
  unfold tailWord_3866997
  simp only [CollatzResearch.WordTrace]
  refine ⟨141040967571537774353151245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94027311714358516235434163 141040967571537774353151245)
  ·
    refine ⟨52890362839326665382431717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141040967571537774353151245 52890362839326665382431717)
    ·
      refine ⟨9916943032373749759205947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52890362839326665382431717 9916943032373749759205947)
      ·
        refine ⟨14875414548560624638808921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9916943032373749759205947 14875414548560624638808921)
        ·
          refine ⟨11156560911420468479106691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14875414548560624638808921 11156560911420468479106691)
          ·
            refine ⟨16734841367130702718660037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156560911420468479106691 16734841367130702718660037)
            ·
              refine ⟨3137782756337006759748757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16734841367130702718660037 3137782756337006759748757)
              ·
                refine ⟨147083566703297191863223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3137782756337006759748757 147083566703297191863223)
                ·
                  rfl

theorem cell22_3866997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 6].length) (baseStart_3866997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3866997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3866997 prefixEnd_3866997 := by exact prefixLift 3866997
  have htrace : WordTrace (prefixWord ++ tailWord_3866997) baseStart_3866997 baseEnd_3866997 := by
    simpa [prefixWord, tailWord_3866997, baseEnd_3866997] using wordTrace_append hprefix tailTrace_3866997
  have hstable : (prefixWord ++ tailWord_3866997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866997).length < 2 ^ (prefixWord ++ tailWord_3866997).sum := by decide
  have hdescent : baseEnd_3866997 < baseStart_3866997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867042 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3867042 : Nat := 118140960795 + 3867042 * 2 ^ 59
def prefixEnd_3867042 : Nat := 4983230072969 + 3 ^ 40 * 3867042 * 2
def baseEnd_3867042 : Nat := 441255834916436536464623

theorem tailTrace_3867042 : CollatzResearch.WordTrace tailWord_3867042 prefixEnd_3867042 441255834916436536464623 := by
  unfold tailWord_3867042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35260652214093686759634845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94028405904249831359026253 35260652214093686759634845)
  ·
    refine ⟨13222744580285132534863067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35260652214093686759634845 13222744580285132534863067)
    ·
      refine ⟨19834116870427698802294601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13222744580285132534863067 19834116870427698802294601)
      ·
        refine ⟨14875587652820774101720951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19834116870427698802294601 14875587652820774101720951)
        ·
          refine ⟨22313381479231161152581427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14875587652820774101720951 22313381479231161152581427)
          ·
            refine ⟨33470072218846741728872141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22313381479231161152581427 33470072218846741728872141)
            ·
              refine ⟨12551277082067528148327053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33470072218846741728872141 12551277082067528148327053)
              ·
                refine ⟨4706728905775323055622645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12551277082067528148327053 4706728905775323055622645)
                ·
                  refine ⟨441255834916436536464623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706728905775323055622645 441255834916436536464623)
                  ·
                    rfl

theorem cell22_3867042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3867042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867042 prefixEnd_3867042 := by exact prefixLift 3867042
  have htrace : WordTrace (prefixWord ++ tailWord_3867042) baseStart_3867042 baseEnd_3867042 := by
    simpa [prefixWord, tailWord_3867042, baseEnd_3867042] using wordTrace_append hprefix tailTrace_3867042
  have hstable : (prefixWord ++ tailWord_3867042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867042).length < 2 ^ (prefixWord ++ tailWord_3867042).sum := by decide
  have hdescent : baseEnd_3867042 < baseStart_3867042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867145 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_3867145 : Nat := 118140960795 + 3867145 * 2 ^ 59
def prefixEnd_3867145 : Nat := 4983230072969 + 3 ^ 40 * 3867145 * 2
def baseEnd_3867145 : Nat := 1323802763754251674068553

theorem tailTrace_3867145 : CollatzResearch.WordTrace tailWord_3867145 prefixEnd_3867145 1323802763754251674068553 := by
  unfold tailWord_3867145
  simp only [CollatzResearch.WordTrace]
  refine ⟨141046365575001595629538889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94030910383334397086359259 141046365575001595629538889)
  ·
    refine ⟨105784774181251196722154167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141046365575001595629538889 105784774181251196722154167)
    ·
      refine ⟨158677161271876795083231251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105784774181251196722154167 158677161271876795083231251)
      ·
        refine ⟨238015741907815192624846877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158677161271876795083231251 238015741907815192624846877)
        ·
          refine ⟨89255903215430697234317579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238015741907815192624846877 89255903215430697234317579)
          ·
            refine ⟨133883854823146045851476369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89255903215430697234317579 133883854823146045851476369)
            ·
              refine ⟨100412891117359534388607277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133883854823146045851476369 100412891117359534388607277)
              ·
                refine ⟨37654834169009825395727729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100412891117359534388607277 37654834169009825395727729)
                ·
                  refine ⟨28241125626757369046795797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37654834169009825395727729 28241125626757369046795797)
                  ·
                    refine ⟨1323802763754251674068553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28241125626757369046795797 1323802763754251674068553)
                    ·
                      rfl

theorem cell22_3867145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_3867145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867145 prefixEnd_3867145 := by exact prefixLift 3867145
  have htrace : WordTrace (prefixWord ++ tailWord_3867145) baseStart_3867145 baseEnd_3867145 := by
    simpa [prefixWord, tailWord_3867145, baseEnd_3867145] using wordTrace_append hprefix tailTrace_3867145
  have hstable : (prefixWord ++ tailWord_3867145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867145).length < 2 ^ (prefixWord ++ tailWord_3867145).sum := by decide
  have hdescent : baseEnd_3867145 < baseStart_3867145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867164 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3867164 : Nat := 118140960795 + 3867164 * 2 ^ 59
def prefixEnd_3867164 : Nat := 4983230072969 + 3 ^ 40 * 3867164 * 2
def baseEnd_3867164 : Nat := 1323809267842541957843495

theorem tailTrace_3867164 : CollatzResearch.WordTrace tailWord_3867164 prefixEnd_3867164 1323809267842541957843495 := by
  unfold tailWord_3867164
  simp only [CollatzResearch.WordTrace]
  refine ⟨70523529280966380937240273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94031372374621841249653697 70523529280966380937240273)
  ·
    refine ⟨52892646960724785702930205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70523529280966380937240273 52892646960724785702930205)
    ·
      refine ⟨19834742610271794638598827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52892646960724785702930205 19834742610271794638598827)
      ·
        refine ⟨29752113915407691957898241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19834742610271794638598827 29752113915407691957898241)
        ·
          refine ⟨22314085436555768968423681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29752113915407691957898241 22314085436555768968423681)
          ·
            refine ⟨16735564077416826726317761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22314085436555768968423681 16735564077416826726317761)
            ·
              refine ⟨12551673058062620044738321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16735564077416826726317761 12551673058062620044738321)
              ·
                refine ⟨9413754793546965033553741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12551673058062620044738321 9413754793546965033553741)
                ·
                  refine ⟨3530158047580111887582653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9413754793546965033553741 3530158047580111887582653)
                  ·
                    refine ⟨1323809267842541957843495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530158047580111887582653 1323809267842541957843495)
                    ·
                      rfl

theorem cell22_3867164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3867164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867164 prefixEnd_3867164 := by exact prefixLift 3867164
  have htrace : WordTrace (prefixWord ++ tailWord_3867164) baseStart_3867164 baseEnd_3867164 := by
    simpa [prefixWord, tailWord_3867164, baseEnd_3867164] using wordTrace_append hprefix tailTrace_3867164
  have hstable : (prefixWord ++ tailWord_3867164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867164).length < 2 ^ (prefixWord ++ tailWord_3867164).sum := by decide
  have hdescent : baseEnd_3867164 < baseStart_3867164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867204 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3867204 : Nat := 118140960795 + 3867204 * 2 ^ 59
def prefixEnd_3867204 : Nat := 4983230072969 + 3 ^ 40 * 3867204 * 2
def baseEnd_3867204 : Nat := 1323822960659995186843373

theorem tailTrace_3867204 : CollatzResearch.WordTrace tailWord_3867204 prefixEnd_3867204 1323822960659995186843373 := by
  unfold tailWord_3867204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70524258740893924352968333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94032344987858565803957777 70524258740893924352968333)
  ·
    refine ⟨26446597027835221632363125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70524258740893924352968333 26446597027835221632363125)
    ·
      refine ⟨2479368471359552028034043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26446597027835221632363125 2479368471359552028034043)
      ·
        refine ⟨3719052707039328042051065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479368471359552028034043 3719052707039328042051065)
        ·
          refine ⟨2789289530279496031538299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3719052707039328042051065 2789289530279496031538299)
          ·
            refine ⟨4183934295419244047307449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789289530279496031538299 4183934295419244047307449)
            ·
              refine ⟨3137950721564433035480587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183934295419244047307449 3137950721564433035480587)
              ·
                refine ⟨4706926082346649553220881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137950721564433035480587 4706926082346649553220881)
                ·
                  refine ⟨3530194561759987164915661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4706926082346649553220881 3530194561759987164915661)
                  ·
                    refine ⟨1323822960659995186843373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530194561759987164915661 1323822960659995186843373)
                    ·
                      rfl

theorem cell22_3867204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3867204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867204 prefixEnd_3867204 := by exact prefixLift 3867204
  have htrace : WordTrace (prefixWord ++ tailWord_3867204) baseStart_3867204 baseEnd_3867204 := by
    simpa [prefixWord, tailWord_3867204, baseEnd_3867204] using wordTrace_append hprefix tailTrace_3867204
  have hstable : (prefixWord ++ tailWord_3867204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867204).length < 2 ^ (prefixWord ++ tailWord_3867204).sum := by decide
  have hdescent : baseEnd_3867204 < baseStart_3867204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867224 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_3867224 : Nat := 118140960795 + 3867224 * 2 ^ 59
def prefixEnd_3867224 : Nat := 4983230072969 + 3 ^ 40 * 3867224 * 2
def baseEnd_3867224 : Nat := 1323829807068721801343311

theorem tailTrace_3867224 : CollatzResearch.WordTrace tailWord_3867224 prefixEnd_3867224 1323829807068721801343311 := by
  unfold tailWord_3867224
  simp only [CollatzResearch.WordTrace]
  refine ⟨70524623470857696060832363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94032831294476928081109817 70524623470857696060832363)
  ·
    refine ⟨105786935206286544091248545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70524623470857696060832363 105786935206286544091248545)
    ·
      refine ⟨79340201404714908068436409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105786935206286544091248545 79340201404714908068436409)
      ·
        refine ⟨59505151053536181051327307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79340201404714908068436409 59505151053536181051327307)
        ·
          refine ⟨89257726580304271576990961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59505151053536181051327307 89257726580304271576990961)
          ·
            refine ⟨66943294935228203682743221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89257726580304271576990961 66943294935228203682743221)
            ·
              refine ⟨6275933900177644095257177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66943294935228203682743221 6275933900177644095257177)
              ·
                refine ⟨4706950425133233071442883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275933900177644095257177 4706950425133233071442883)
                ·
                  refine ⟨7060425637699849607164325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706950425133233071442883 7060425637699849607164325)
                  ·
                    refine ⟨1323829807068721801343311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7060425637699849607164325 1323829807068721801343311)
                    ·
                      rfl

theorem cell22_3867224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_3867224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867224 prefixEnd_3867224 := by exact prefixLift 3867224
  have htrace : WordTrace (prefixWord ++ tailWord_3867224) baseStart_3867224 baseEnd_3867224 := by
    simpa [prefixWord, tailWord_3867224, baseEnd_3867224] using wordTrace_append hprefix tailTrace_3867224
  have hstable : (prefixWord ++ tailWord_3867224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867224).length < 2 ^ (prefixWord ++ tailWord_3867224).sum := by decide
  have hdescent : baseEnd_3867224 < baseStart_3867224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867239 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 4]
def baseStart_3867239 : Nat := 118140960795 + 3867239 * 2 ^ 59
def prefixEnd_3867239 : Nat := 4983230072969 + 3 ^ 40 * 3867239 * 2
def baseEnd_3867239 : Nat := 441278313958422254072755

theorem tailTrace_3867239 : CollatzResearch.WordTrace tailWord_3867239 prefixEnd_3867239 441278313958422254072755 := by
  unfold tailWord_3867239
  simp only [CollatzResearch.WordTrace]
  refine ⟨141049794036661049683460771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94033196024440699788973847 141049794036661049683460771)
  ·
    refine ⟨211574691054991574525191157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141049794036661049683460771 211574691054991574525191157)
    ·
      refine ⟨19835127286405460111736671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211574691054991574525191157 19835127286405460111736671)
      ·
        refine ⟨29752690929608190167605007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19835127286405460111736671 29752690929608190167605007)
        ·
          refine ⟨44629036394412285251407511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29752690929608190167605007 44629036394412285251407511)
          ·
            refine ⟨66943554591618427877111267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44629036394412285251407511 66943554591618427877111267)
            ·
              refine ⟨100415331887427641815666901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66943554591618427877111267 100415331887427641815666901)
              ·
                refine ⟨2353484341111585355054693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100415331887427641815666901 2353484341111585355054693)
                ·
                  refine ⟨441278313958422254072755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353484341111585355054693 441278313958422254072755)
                  ·
                    rfl

theorem cell22_3867239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 4].length) (baseStart_3867239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867239 prefixEnd_3867239 := by exact prefixLift 3867239
  have htrace : WordTrace (prefixWord ++ tailWord_3867239) baseStart_3867239 baseEnd_3867239 := by
    simpa [prefixWord, tailWord_3867239, baseEnd_3867239] using wordTrace_append hprefix tailTrace_3867239
  have hstable : (prefixWord ++ tailWord_3867239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867239).length < 2 ^ (prefixWord ++ tailWord_3867239).sum := by decide
  have hdescent : baseEnd_3867239 < baseStart_3867239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867267 : List Nat := [1, 1, 1, 3, 3, 1, 5, 7]
def baseStart_3867267 : Nat := 118140960795 + 3867267 * 2 ^ 59
def prefixEnd_3867267 : Nat := 4983230072969 + 3 ^ 40 * 3867267 * 2
def baseEnd_3867267 : Nat := 147093836316387113613131

theorem tailTrace_3867267 : CollatzResearch.WordTrace tailWord_3867267 prefixEnd_3867267 147093836316387113613131 := by
  unfold tailWord_3867267
  simp only [CollatzResearch.WordTrace]
  refine ⟨141050815280559610465480055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94033876853706406976986703 141050815280559610465480055)
  ·
    refine ⟨211576222920839415698220083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141050815280559610465480055 211576222920839415698220083)
    ·
      refine ⟨317364334381259123547330125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211576222920839415698220083 317364334381259123547330125)
      ·
        refine ⟨119011625392972171330248797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317364334381259123547330125 119011625392972171330248797)
        ·
          refine ⟨44629359522364564248843299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119011625392972171330248797 44629359522364564248843299)
          ·
            refine ⟨66944039283546846373264949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44629359522364564248843299 66944039283546846373264949)
            ·
              refine ⟨6276003682832516847493589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66944039283546846373264949 6276003682832516847493589)
              ·
                refine ⟨147093836316387113613131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6276003682832516847493589 147093836316387113613131)
                ·
                  rfl

theorem cell22_3867267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 7].length) (baseStart_3867267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867267 prefixEnd_3867267 := by exact prefixLift 3867267
  have htrace : WordTrace (prefixWord ++ tailWord_3867267) baseStart_3867267 baseEnd_3867267 := by
    simpa [prefixWord, tailWord_3867267, baseEnd_3867267] using wordTrace_append hprefix tailTrace_3867267
  have hstable : (prefixWord ++ tailWord_3867267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867267).length < 2 ^ (prefixWord ++ tailWord_3867267).sum := by decide
  have hdescent : baseEnd_3867267 < baseStart_3867267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867380 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3867380 : Nat := 118140960795 + 3867380 * 2 ^ 59
def prefixEnd_3867380 : Nat := 4983230072969 + 3 ^ 40 * 3867380 * 2
def baseEnd_3867380 : Nat := 441294403018929798147611

theorem tailTrace_3867380 : CollatzResearch.WordTrace tailWord_3867380 prefixEnd_3867380 441294403018929798147611 := by
  unfold tailWord_3867380
  simp only [CollatzResearch.WordTrace]
  refine ⟨70527468364575115382171797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94036624486100153842895729 70527468364575115382171797)
  ·
    refine ⟨3305975079589458533539303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70527468364575115382171797 3305975079589458533539303)
    ·
      refine ⟨4958962619384187800308955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3305975079589458533539303 4958962619384187800308955)
      ·
        refine ⟨7438443929076281700463433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958962619384187800308955 7438443929076281700463433)
        ·
          refine ⟨5578832946807211275347575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438443929076281700463433 5578832946807211275347575)
          ·
            refine ⟨8368249420210816913021363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578832946807211275347575 8368249420210816913021363)
            ·
              refine ⟨12552374130316225369532045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368249420210816913021363 12552374130316225369532045)
              ·
                refine ⟨4707140298868584513574517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12552374130316225369532045 4707140298868584513574517)
                ·
                  refine ⟨441294403018929798147611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707140298868584513574517 441294403018929798147611)
                  ·
                    rfl

theorem cell22_3867380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3867380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867380 prefixEnd_3867380 := by exact prefixLift 3867380
  have htrace : WordTrace (prefixWord ++ tailWord_3867380) baseStart_3867380 baseEnd_3867380 := by
    simpa [prefixWord, tailWord_3867380, baseEnd_3867380] using wordTrace_append hprefix tailTrace_3867380
  have hstable : (prefixWord ++ tailWord_3867380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867380).length < 2 ^ (prefixWord ++ tailWord_3867380).sum := by decide
  have hdescent : baseEnd_3867380 < baseStart_3867380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867389 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3867389 : Nat := 118140960795 + 3867389 * 2 ^ 59
def prefixEnd_3867389 : Nat := 4983230072969 + 3 ^ 40 * 3867389 * 2
def baseEnd_3867389 : Nat := 1323886289940716370967805

theorem tailTrace_3867389 : CollatzResearch.WordTrace tailWord_3867389 prefixEnd_3867389 1323886289940716370967805 := by
  unfold tailWord_3867389
  simp only [CollatzResearch.WordTrace]
  refine ⟨141055264986117625301421221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94036843324078416867614147 141055264986117625301421221)
  ·
    refine ⟨26447862184897054744016479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141055264986117625301421221 26447862184897054744016479)
    ·
      refine ⟨39671793277345582116024719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26447862184897054744016479 39671793277345582116024719)
      ·
        refine ⟨59507689916018373174037079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39671793277345582116024719 59507689916018373174037079)
        ·
          refine ⟨89261534874027559761055619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59507689916018373174037079 89261534874027559761055619)
          ·
            refine ⟨133892302311041339641583429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89261534874027559761055619 133892302311041339641583429)
            ·
              refine ⟨25104806683320251182796893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133892302311041339641583429 25104806683320251182796893)
              ·
                refine ⟨9414302506245094193548835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25104806683320251182796893 9414302506245094193548835)
                ·
                  refine ⟨14121453759367641290323253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414302506245094193548835 14121453759367641290323253)
                  ·
                    refine ⟨1323886289940716370967805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14121453759367641290323253 1323886289940716370967805)
                    ·
                      rfl

theorem cell22_3867389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3867389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867389 prefixEnd_3867389 := by exact prefixLift 3867389
  have htrace : WordTrace (prefixWord ++ tailWord_3867389) baseStart_3867389 baseEnd_3867389 := by
    simpa [prefixWord, tailWord_3867389, baseEnd_3867389] using wordTrace_append hprefix tailTrace_3867389
  have hstable : (prefixWord ++ tailWord_3867389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867389).length < 2 ^ (prefixWord ++ tailWord_3867389).sum := by decide
  have hdescent : baseEnd_3867389 < baseStart_3867389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867423 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 2, 3]
def baseStart_3867423 : Nat := 118140960795 + 3867423 * 2 ^ 59
def prefixEnd_3867423 : Nat := 4983230072969 + 3 ^ 40 * 3867423 * 2
def baseEnd_3867423 : Nat := 1323897928835551615617701

theorem tailTrace_3867423 : CollatzResearch.WordTrace tailWord_3867423 prefixEnd_3867423 1323897928835551615617701 := by
  unfold tailWord_3867423
  simp only [CollatzResearch.WordTrace]
  refine ⟨141056505067994449108158923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94037670045329632738772615 141056505067994449108158923)
  ·
    refine ⟨211584757601991673662238385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141056505067994449108158923 211584757601991673662238385)
    ·
      refine ⟨158688568201493755246678789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211584757601991673662238385 158688568201493755246678789)
      ·
        refine ⟨29754106537780079108752273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158688568201493755246678789 29754106537780079108752273)
        ·
          refine ⟨22315579903335059331564205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29754106537780079108752273 22315579903335059331564205)
          ·
            refine ⟨8368342463750647249336577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22315579903335059331564205 8368342463750647249336577)
            ·
              refine ⟨6276256847812985437002433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8368342463750647249336577 6276256847812985437002433)
              ·
                refine ⟨4707192635859739077751825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6276256847812985437002433 4707192635859739077751825)
                ·
                  refine ⟨3530394476894804308313869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4707192635859739077751825 3530394476894804308313869)
                  ·
                    refine ⟨1323897928835551615617701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530394476894804308313869 1323897928835551615617701)
                    ·
                      rfl

theorem cell22_3867423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_3867423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867423 prefixEnd_3867423 := by exact prefixLift 3867423
  have htrace : WordTrace (prefixWord ++ tailWord_3867423) baseStart_3867423 baseEnd_3867423 := by
    simpa [prefixWord, tailWord_3867423, baseEnd_3867423] using wordTrace_append hprefix tailTrace_3867423
  have hstable : (prefixWord ++ tailWord_3867423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867423).length < 2 ^ (prefixWord ++ tailWord_3867423).sum := by decide
  have hdescent : baseEnd_3867423 < baseStart_3867423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867453 : List Nat := [1, 4, 1, 4, 2, 1, 3, 6]
def baseStart_3867453 : Nat := 118140960795 + 3867453 * 2 ^ 59
def prefixEnd_3867453 : Nat := 4983230072969 + 3 ^ 40 * 3867453 * 2
def baseEnd_3867453 : Nat := 147100910938737948596401

theorem tailTrace_3867453 : CollatzResearch.WordTrace tailWord_3867453 prefixEnd_3867453 147100910938737948596401 := by
  unfold tailWord_3867453
  simp only [CollatzResearch.WordTrace]
  refine ⟨141057599257885764231751013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94038399505257176154500675 141057599257885764231751013)
  ·
    refine ⟨26448299860853580793453315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141057599257885764231751013 26448299860853580793453315)
    ·
      refine ⟨39672449791280371190179973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26448299860853580793453315 39672449791280371190179973)
      ·
        refine ⟨7438584335865069598158745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39672449791280371190179973 7438584335865069598158745)
        ·
          refine ⟨5578938251898802198619059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438584335865069598158745 5578938251898802198619059)
          ·
            refine ⟨8368407377848203297928589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578938251898802198619059 8368407377848203297928589)
            ·
              refine ⟨3138152766693076236723221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8368407377848203297928589 3138152766693076236723221)
              ·
                refine ⟨147100910938737948596401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3138152766693076236723221 147100910938737948596401)
                ·
                  rfl

theorem cell22_3867453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 6].length) (baseStart_3867453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867453 prefixEnd_3867453 := by exact prefixLift 3867453
  have htrace : WordTrace (prefixWord ++ tailWord_3867453) baseStart_3867453 baseEnd_3867453 := by
    simpa [prefixWord, tailWord_3867453, baseEnd_3867453] using wordTrace_append hprefix tailTrace_3867453
  have hstable : (prefixWord ++ tailWord_3867453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867453).length < 2 ^ (prefixWord ++ tailWord_3867453).sum := by decide
  have hdescent : baseEnd_3867453 < baseStart_3867453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867464 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_3867464 : Nat := 118140960795 + 3867464 * 2 ^ 59
def prefixEnd_3867464 : Nat := 4983230072969 + 3 ^ 40 * 3867464 * 2
def baseEnd_3867464 : Nat := 441303987991147058447525

theorem tailTrace_3867464 : CollatzResearch.WordTrace tailWord_3867464 prefixEnd_3867464 441303987991147058447525 := by
  unfold tailWord_3867464
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529000230422956555200723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94038666973897275406934297 70529000230422956555200723)
  ·
    refine ⟨105793500345634434832801085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70529000230422956555200723 105793500345634434832801085)
    ·
      refine ⟨39672562629612913062300407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105793500345634434832801085 39672562629612913062300407)
      ·
        refine ⟨59508843944419369593450611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39672562629612913062300407 59508843944419369593450611)
        ·
          refine ⟨89263265916629054390175917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59508843944419369593450611 89263265916629054390175917)
          ·
            refine ⟨33473724718735895396315969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89263265916629054390175917 33473724718735895396315969)
            ·
              refine ⟨25105293539051921547236977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33473724718735895396315969 25105293539051921547236977)
              ·
                refine ⟨18828970154288941160427733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25105293539051921547236977 18828970154288941160427733)
                ·
                  refine ⟨441303987991147058447525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18828970154288941160427733 441303987991147058447525)
                  ·
                    rfl

theorem cell22_3867464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_3867464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867464 prefixEnd_3867464 := by exact prefixLift 3867464
  have htrace : WordTrace (prefixWord ++ tailWord_3867464) baseStart_3867464 baseEnd_3867464 := by
    simpa [prefixWord, tailWord_3867464, baseEnd_3867464] using wordTrace_append hprefix tailTrace_3867464
  have hstable : (prefixWord ++ tailWord_3867464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867464).length < 2 ^ (prefixWord ++ tailWord_3867464).sum := by decide
  have hdescent : baseEnd_3867464 < baseStart_3867464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867481 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 5]
def baseStart_3867481 : Nat := 118140960795 + 3867481 * 2 ^ 59
def prefixEnd_3867481 : Nat := 4983230072969 + 3 ^ 40 * 3867481 * 2
def baseEnd_3867481 : Nat := 441305927806952932555841

theorem tailTrace_3867481 : CollatzResearch.WordTrace tailWord_3867481 prefixEnd_3867481 441305927806952932555841 := by
  unfold tailWord_3867481
  simp only [CollatzResearch.WordTrace]
  refine ⟨141058620501784325013770297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94039080334522883342513531 141058620501784325013770297)
  ·
    refine ⟨105793965376338243760327723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141058620501784325013770297 105793965376338243760327723)
    ·
      refine ⟨158690948064507365640491585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105793965376338243760327723 158690948064507365640491585)
      ·
        refine ⟨119018211048380524230368689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158690948064507365640491585 119018211048380524230368689)
        ·
          refine ⟨89263658286285393172776517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119018211048380524230368689 89263658286285393172776517)
          ·
            refine ⟨16736935928678511219895597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89263658286285393172776517 16736935928678511219895597)
            ·
              refine ⟨6276350973254441707460849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16736935928678511219895597 6276350973254441707460849)
              ·
                refine ⟨4707263229940831280595637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6276350973254441707460849 4707263229940831280595637)
                ·
                  refine ⟨441305927806952932555841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707263229940831280595637 441305927806952932555841)
                  ·
                    rfl

theorem cell22_3867481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_3867481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867481 prefixEnd_3867481 := by exact prefixLift 3867481
  have htrace : WordTrace (prefixWord ++ tailWord_3867481) baseStart_3867481 baseEnd_3867481 := by
    simpa [prefixWord, tailWord_3867481, baseEnd_3867481] using wordTrace_append hprefix tailTrace_3867481
  have hstable : (prefixWord ++ tailWord_3867481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867481).length < 2 ^ (prefixWord ++ tailWord_3867481).sum := by decide
  have hdescent : baseEnd_3867481 < baseStart_3867481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867496 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3867496 : Nat := 118140960795 + 3867496 * 2 ^ 59
def prefixEnd_3867496 : Nat := 4983230072969 + 3 ^ 40 * 3867496 * 2
def baseEnd_3867496 : Nat := 1323922918227403758542477

theorem tailTrace_3867496 : CollatzResearch.WordTrace tailWord_3867496 prefixEnd_3867496 1323922918227403758542477 := by
  unfold tailWord_3867496
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529583798364991287783171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94039445064486655050377561 70529583798364991287783171)
  ·
    refine ⟨105794375697547486931674757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70529583798364991287783171 105794375697547486931674757)
    ·
      refine ⟨19836445443290153799689017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105794375697547486931674757 19836445443290153799689017)
      ·
        refine ⟨14877334082467615349766763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19836445443290153799689017 14877334082467615349766763)
        ·
          refine ⟨22316001123701423024650145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14877334082467615349766763 22316001123701423024650145)
          ·
            refine ⟨16737000842776067268487609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22316001123701423024650145 16737000842776067268487609)
            ·
              refine ⟨12552750632082050451365707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16737000842776067268487609 12552750632082050451365707)
              ·
                refine ⟨18829125948123075677048561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12552750632082050451365707 18829125948123075677048561)
                ·
                  refine ⟨14121844461092306757786421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18829125948123075677048561 14121844461092306757786421)
                  ·
                    refine ⟨1323922918227403758542477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14121844461092306757786421 1323922918227403758542477)
                    ·
                      rfl

theorem cell22_3867496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3867496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867496 prefixEnd_3867496 := by exact prefixLift 3867496
  have htrace : WordTrace (prefixWord ++ tailWord_3867496) baseStart_3867496 baseEnd_3867496 := by
    simpa [prefixWord, tailWord_3867496, baseEnd_3867496] using wordTrace_append hprefix tailTrace_3867496
  have hstable : (prefixWord ++ tailWord_3867496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867496).length < 2 ^ (prefixWord ++ tailWord_3867496).sum := by decide
  have hdescent : baseEnd_3867496 < baseStart_3867496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867528 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_3867528 : Nat := 118140960795 + 3867528 * 2 ^ 59
def prefixEnd_3867528 : Nat := 4983230072969 + 3 ^ 40 * 3867528 * 2
def baseEnd_3867528 : Nat := 1323933872481366341742379

theorem tailTrace_3867528 : CollatzResearch.WordTrace tailWord_3867528 prefixEnd_3867528 1323933872481366341742379 := by
  unfold tailWord_3867528
  simp only [CollatzResearch.WordTrace]
  refine ⟨70530167366307026020365619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94040223155076034693820825 70530167366307026020365619)
  ·
    refine ⟨105795251049460539030548429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70530167366307026020365619 105795251049460539030548429)
    ·
      refine ⟨39673219143547702136455661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105795251049460539030548429 39673219143547702136455661)
      ·
        refine ⟨14877457178830388301170873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39673219143547702136455661 14877457178830388301170873)
        ·
          refine ⟨11158092884122791225878155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14877457178830388301170873 11158092884122791225878155)
          ·
            refine ⟨16737139326184186838817233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11158092884122791225878155 16737139326184186838817233)
            ·
              refine ⟨12552854494638140129112925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16737139326184186838817233 12552854494638140129112925)
              ·
                refine ⟨4707320435489302548417347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12552854494638140129112925 4707320435489302548417347)
                ·
                  refine ⟨7060980653233953822626021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707320435489302548417347 7060980653233953822626021)
                  ·
                    refine ⟨1323933872481366341742379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7060980653233953822626021 1323933872481366341742379)
                    ·
                      rfl

theorem cell22_3867528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_3867528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867528 prefixEnd_3867528 := by exact prefixLift 3867528
  have htrace : WordTrace (prefixWord ++ tailWord_3867528) baseStart_3867528 baseEnd_3867528 := by
    simpa [prefixWord, tailWord_3867528, baseEnd_3867528] using wordTrace_append hprefix tailTrace_3867528
  have hstable : (prefixWord ++ tailWord_3867528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867528).length < 2 ^ (prefixWord ++ tailWord_3867528).sum := by decide
  have hdescent : baseEnd_3867528 < baseStart_3867528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867539 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_3867539 : Nat := 118140960795 + 3867539 * 2 ^ 59
def prefixEnd_3867539 : Nat := 4983230072969 + 3 ^ 40 * 3867539 * 2
def baseEnd_3867539 : Nat := 1323937638006165979717345

theorem tailTrace_3867539 : CollatzResearch.WordTrace tailWord_3867539 prefixEnd_3867539 1323937638006165979717345 := by
  unfold tailWord_3867539
  simp only [CollatzResearch.WordTrace]
  refine ⟨141060735935574200919381671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94040490623716133946254447 141060735935574200919381671)
  ·
    refine ⟨211591103903361301379072507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141060735935574200919381671 211591103903361301379072507)
    ·
      refine ⟨317386655855041952068608761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211591103903361301379072507 317386655855041952068608761)
      ·
        refine ⟨238039991891281464051456571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317386655855041952068608761 238039991891281464051456571)
        ·
          refine ⟨357059987836922196077184857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238039991891281464051456571 357059987836922196077184857)
          ·
            refine ⟨267794990877691647057888643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357059987836922196077184857 267794990877691647057888643)
            ·
              refine ⟨401692486316537470586832965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267794990877691647057888643 401692486316537470586832965)
              ·
                refine ⟨75317341184350775735031181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401692486316537470586832965 75317341184350775735031181)
                ·
                  refine ⟨28244002944131540900636693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75317341184350775735031181 28244002944131540900636693)
                  ·
                    refine ⟨1323937638006165979717345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28244002944131540900636693 1323937638006165979717345)
                    ·
                      rfl

theorem cell22_3867539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_3867539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867539 prefixEnd_3867539 := by exact prefixLift 3867539
  have htrace : WordTrace (prefixWord ++ tailWord_3867539) baseStart_3867539 baseEnd_3867539 := by
    simpa [prefixWord, tailWord_3867539, baseEnd_3867539] using wordTrace_append hprefix tailTrace_3867539
  have hstable : (prefixWord ++ tailWord_3867539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867539).length < 2 ^ (prefixWord ++ tailWord_3867539).sum := by decide
  have hdescent : baseEnd_3867539 < baseStart_3867539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867556 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3867556 : Nat := 118140960795 + 3867556 * 2 ^ 59
def prefixEnd_3867556 : Nat := 4983230072969 + 3 ^ 40 * 3867556 * 2
def baseEnd_3867556 : Nat := 1323943457453583602042293

theorem tailTrace_3867556 : CollatzResearch.WordTrace tailWord_3867556 prefixEnd_3867556 1323943457453583602042293 := by
  unfold tailWord_3867556
  simp only [CollatzResearch.WordTrace]
  refine ⟨70530677988256306411375261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94040903984341741881833681 70530677988256306411375261)
  ·
    refine ⟨26449004245596114904265723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70530677988256306411375261 26449004245596114904265723)
    ·
      refine ⟨39673506368394172356398585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26449004245596114904265723 39673506368394172356398585)
      ·
        refine ⟨29755129776295629267298939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39673506368394172356398585 29755129776295629267298939)
        ·
          refine ⟨44632694664443443900948409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29755129776295629267298939 44632694664443443900948409)
          ·
            refine ⟨33474520998332582925711307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44632694664443443900948409 33474520998332582925711307)
            ·
              refine ⟨50211781497498874388566961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33474520998332582925711307 50211781497498874388566961)
              ·
                refine ⟨37658836123124155791425221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50211781497498874388566961 37658836123124155791425221)
                ·
                  refine ⟨7061031773085779210892229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37658836123124155791425221 7061031773085779210892229)
                  ·
                    refine ⟨1323943457453583602042293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7061031773085779210892229 1323943457453583602042293)
                    ·
                      rfl

theorem cell22_3867556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3867556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867556 prefixEnd_3867556 := by exact prefixLift 3867556
  have htrace : WordTrace (prefixWord ++ tailWord_3867556) baseStart_3867556 baseEnd_3867556 := by
    simpa [prefixWord, tailWord_3867556, baseEnd_3867556] using wordTrace_append hprefix tailTrace_3867556
  have hstable : (prefixWord ++ tailWord_3867556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867556).length < 2 ^ (prefixWord ++ tailWord_3867556).sum := by decide
  have hdescent : baseEnd_3867556 < baseStart_3867556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867573 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3867573 : Nat := 118140960795 + 3867573 * 2 ^ 59
def prefixEnd_3867573 : Nat := 4983230072969 + 3 ^ 40 * 3867573 * 2
def baseEnd_3867573 : Nat := 1323949276901001224367241

theorem tailTrace_3867573 : CollatzResearch.WordTrace tailWord_3867573 prefixEnd_3867573 1323949276901001224367241 := by
  unfold tailWord_3867573
  simp only [CollatzResearch.WordTrace]
  refine ⟨141061976017451024726119373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94041317344967349817412915 141061976017451024726119373)
  ·
    refine ⟨52898241006544134272294765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141061976017451024726119373 52898241006544134272294765)
    ·
      refine ⟨19836840377454050352110537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52898241006544134272294765 19836840377454050352110537)
      ·
        refine ⟨14877630283090537764082903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19836840377454050352110537 14877630283090537764082903)
        ·
          refine ⟨22316445424635806646124355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14877630283090537764082903 22316445424635806646124355)
          ·
            refine ⟨33474668136953709969186533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22316445424635806646124355 33474668136953709969186533)
            ·
              refine ⟨6276500275678820619222475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33474668136953709969186533 6276500275678820619222475)
              ·
                refine ⟨9414750413518230928833713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276500275678820619222475 9414750413518230928833713)
                ·
                  refine ⟨7061062810138673196625285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414750413518230928833713 7061062810138673196625285)
                  ·
                    refine ⟨1323949276901001224367241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7061062810138673196625285 1323949276901001224367241)
                    ·
                      rfl

theorem cell22_3867573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3867573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867573 prefixEnd_3867573 := by exact prefixLift 3867573
  have htrace : WordTrace (prefixWord ++ tailWord_3867573) baseStart_3867573 baseEnd_3867573 := by
    simpa [prefixWord, tailWord_3867573, baseEnd_3867573] using wordTrace_append hprefix tailTrace_3867573
  have hstable : (prefixWord ++ tailWord_3867573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867573).length < 2 ^ (prefixWord ++ tailWord_3867573).sum := by decide
  have hdescent : baseEnd_3867573 < baseStart_3867573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867588 : List Nat := [2, 3, 3, 3, 1, 10]
def baseStart_3867588 : Nat := 118140960795 + 3867588 * 2 ^ 59
def prefixEnd_3867588 : Nat := 4983230072969 + 3 ^ 40 * 3867588 * 2
def baseEnd_3867588 : Nat := 16345116193920323274595

theorem tailTrace_3867588 : CollatzResearch.WordTrace tailWord_3867588 prefixEnd_3867588 16345116193920323274595 := by
  unfold tailWord_3867588
  simp only [CollatzResearch.WordTrace]
  refine ⟨70531261556198341143957709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94041682074931121525276945 70531261556198341143957709)
  ·
    refine ⟨26449223083574377928984141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70531261556198341143957709 26449223083574377928984141)
    ·
      refine ⟨9918458656340391723369053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26449223083574377928984141 9918458656340391723369053)
      ·
        refine ⟨3719421996127646896263395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9918458656340391723369053 3719421996127646896263395)
        ·
          refine ⟨5579132994191470344395093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719421996127646896263395 5579132994191470344395093)
          ·
            refine ⟨16345116193920323274595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5579132994191470344395093 16345116193920323274595)
            ·
              rfl

theorem cell22_3867588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 10].length) (baseStart_3867588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867588 prefixEnd_3867588 := by exact prefixLift 3867588
  have htrace : WordTrace (prefixWord ++ tailWord_3867588) baseStart_3867588 baseEnd_3867588 := by
    simpa [prefixWord, tailWord_3867588, baseEnd_3867588] using wordTrace_append hprefix tailTrace_3867588
  have hstable : (prefixWord ++ tailWord_3867588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867588).length < 2 ^ (prefixWord ++ tailWord_3867588).sum := by decide
  have hdescent : baseEnd_3867588 < baseStart_3867588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867605 : List Nat := [1, 3, 2, 3, 4, 1, 1, 7]
def baseStart_3867605 : Nat := 118140960795 + 3867605 * 2 ^ 59
def prefixEnd_3867605 : Nat := 4983230072969 + 3 ^ 40 * 3867605 * 2
def baseEnd_3867605 : Nat := 147106692350551534174127

theorem tailTrace_3867605 : CollatzResearch.WordTrace tailWord_3867605 prefixEnd_3867605 147106692350551534174127 := by
  unfold tailWord_3867605
  simp only [CollatzResearch.WordTrace]
  refine ⟨141063143153335094191284269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94042095435556729460856179 141063143153335094191284269)
  ·
    refine ⟨52898678682500660321731601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141063143153335094191284269 52898678682500660321731601)
    ·
      refine ⟨39674009011875495241298701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52898678682500660321731601 39674009011875495241298701)
      ·
        refine ⟨14877753379453310715487013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39674009011875495241298701 14877753379453310715487013)
        ·
          refine ⟨2789578758647495759153815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14877753379453310715487013 2789578758647495759153815)
          ·
            refine ⟨4184368137971243638730723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789578758647495759153815 4184368137971243638730723)
            ·
              refine ⟨6276552206956865458096085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184368137971243638730723 6276552206956865458096085)
              ·
                refine ⟨147106692350551534174127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6276552206956865458096085 147106692350551534174127)
                ·
                  rfl

theorem cell22_3867605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 7].length) (baseStart_3867605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867605 prefixEnd_3867605 := by exact prefixLift 3867605
  have htrace : WordTrace (prefixWord ++ tailWord_3867605) baseStart_3867605 baseEnd_3867605 := by
    simpa [prefixWord, tailWord_3867605, baseEnd_3867605] using wordTrace_append hprefix tailTrace_3867605
  have hstable : (prefixWord ++ tailWord_3867605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867605).length < 2 ^ (prefixWord ++ tailWord_3867605).sum := by decide
  have hdescent : baseEnd_3867605 < baseStart_3867605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867691 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_3867691 : Nat := 118140960795 + 3867691 * 2 ^ 59
def prefixEnd_3867691 : Nat := 4983230072969 + 3 ^ 40 * 3867691 * 2
def baseEnd_3867691 : Nat := 1323989670712488249916879

theorem tailTrace_3867691 : CollatzResearch.WordTrace tailWord_3867691 prefixEnd_3867691 1323989670712488249916879 := by
  unfold tailWord_3867691
  simp only [CollatzResearch.WordTrace]
  refine ⟨141066279831023530878914927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94044186554015687252609951 141066279831023530878914927)
  ·
    refine ⟨211599419746535296318372391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141066279831023530878914927 211599419746535296318372391)
    ·
      refine ⟨317399129619802944477558587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211599419746535296318372391 317399129619802944477558587)
      ·
        refine ⟨476098694429704416716337881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317399129619802944477558587 476098694429704416716337881)
        ·
          refine ⟨357074020822278312537253411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476098694429704416716337881 357074020822278312537253411)
          ·
            refine ⟨535611031233417468805880117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357074020822278312537253411 535611031233417468805880117)
            ·
              refine ⟨50213534178132887700551261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 535611031233417468805880117 50213534178132887700551261)
              ·
                refine ⟨18830075316799832887706723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50213534178132887700551261 18830075316799832887706723)
                ·
                  refine ⟨28245112975199749331560085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18830075316799832887706723 28245112975199749331560085)
                  ·
                    refine ⟨1323989670712488249916879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28245112975199749331560085 1323989670712488249916879)
                    ·
                      rfl

theorem cell22_3867691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_3867691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867691 prefixEnd_3867691 := by exact prefixLift 3867691
  have htrace : WordTrace (prefixWord ++ tailWord_3867691) baseStart_3867691 baseEnd_3867691 := by
    simpa [prefixWord, tailWord_3867691, baseEnd_3867691] using wordTrace_append hprefix tailTrace_3867691
  have hstable : (prefixWord ++ tailWord_3867691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867691).length < 2 ^ (prefixWord ++ tailWord_3867691).sum := by decide
  have hdescent : baseEnd_3867691 < baseStart_3867691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867706 : List Nat := [3, 1, 1, 1, 3, 1, 12]
def baseStart_3867706 : Nat := 118140960795 + 3867706 * 2 ^ 59
def prefixEnd_3867706 : Nat := 4983230072969 + 3 ^ 40 * 3867706 * 2
def baseEnd_3867706 : Nat := 49036844648853081881179

theorem tailTrace_3867706 : CollatzResearch.WordTrace tailWord_3867706 prefixEnd_3867706 49036844648853081881179 := by
  unfold tailWord_3867706
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266706731492297110177743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94044551283979458960473981 35266706731492297110177743)
  ·
    refine ⟨52900060097238445665266615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35266706731492297110177743 52900060097238445665266615)
    ·
      refine ⟨79350090145857668497899923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52900060097238445665266615 79350090145857668497899923)
      ·
        refine ⟨119025135218786502746849885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79350090145857668497899923 119025135218786502746849885)
        ·
          refine ⟨44634425707044938530068707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119025135218786502746849885 44634425707044938530068707)
          ·
            refine ⟨66951638560567407795103061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44634425707044938530068707 66951638560567407795103061)
            ·
              refine ⟨49036844648853081881179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 66951638560567407795103061 49036844648853081881179)
              ·
                rfl

theorem cell22_3867706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 12].length) (baseStart_3867706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867706 prefixEnd_3867706 := by exact prefixLift 3867706
  have htrace : WordTrace (prefixWord ++ tailWord_3867706) baseStart_3867706 baseEnd_3867706 := by
    simpa [prefixWord, tailWord_3867706, baseEnd_3867706] using wordTrace_append hprefix tailTrace_3867706
  have hstable : (prefixWord ++ tailWord_3867706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867706).length < 2 ^ (prefixWord ++ tailWord_3867706).sum := by decide
  have hdescent : baseEnd_3867706 < baseStart_3867706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867708 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_3867708 : Nat := 118140960795 + 3867708 * 2 ^ 59
def prefixEnd_3867708 : Nat := 4983230072969 + 3 ^ 40 * 3867708 * 2
def baseEnd_3867708 : Nat := 1323995490159905872241827

theorem tailTrace_3867708 : CollatzResearch.WordTrace tailWord_3867708 prefixEnd_3867708 1323995490159905872241827 := by
  unfold tailWord_3867708
  simp only [CollatzResearch.WordTrace]
  refine ⟨70533449935980971391141889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94044599914641295188189185 70533449935980971391141889)
  ·
    refine ⟨52900087451985728543356417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70533449935980971391141889 52900087451985728543356417)
    ·
      refine ⟨39675065588989296407517313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52900087451985728543356417 39675065588989296407517313)
      ·
        refine ⟨29756299191741972305637985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39675065588989296407517313 29756299191741972305637985)
        ·
          refine ⟨22317224393806479229228489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29756299191741972305637985 22317224393806479229228489)
          ·
            refine ⟨16737918295354859421921367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22317224393806479229228489 16737918295354859421921367)
            ·
              refine ⟨25106877443032289132882051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16737918295354859421921367 25106877443032289132882051)
              ·
                refine ⟨37660316164548433699323077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25106877443032289132882051 37660316164548433699323077)
                ·
                  refine ⟨7061309280852831318623077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37660316164548433699323077 7061309280852831318623077)
                  ·
                    refine ⟨1323995490159905872241827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7061309280852831318623077 1323995490159905872241827)
                    ·
                      rfl

theorem cell22_3867708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_3867708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867708 prefixEnd_3867708 := by exact prefixLift 3867708
  have htrace : WordTrace (prefixWord ++ tailWord_3867708) baseStart_3867708 baseEnd_3867708 := by
    simpa [prefixWord, tailWord_3867708, baseEnd_3867708] using wordTrace_append hprefix tailTrace_3867708
  have hstable : (prefixWord ++ tailWord_3867708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867708).length < 2 ^ (prefixWord ++ tailWord_3867708).sum := by decide
  have hdescent : baseEnd_3867708 < baseStart_3867708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867721 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_3867721 : Nat := 118140960795 + 3867721 * 2 ^ 59
def prefixEnd_3867721 : Nat := 4983230072969 + 3 ^ 40 * 3867721 * 2
def baseEnd_3867721 : Nat := 1323999940325578171666787

theorem tailTrace_3867721 : CollatzResearch.WordTrace tailWord_3867721 prefixEnd_3867721 1323999940325578171666787 := by
  unfold tailWord_3867721
  simp only [CollatzResearch.WordTrace]
  refine ⟨141067374020914846002507017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94044916013943230668338011 141067374020914846002507017)
  ·
    refine ⟨105800530515686134501880263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141067374020914846002507017 105800530515686134501880263)
    ·
      refine ⟨158700795773529201752820395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105800530515686134501880263 158700795773529201752820395)
      ·
        refine ⟨238051193660293802629230593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158700795773529201752820395 238051193660293802629230593)
        ·
          refine ⟨178538395245220351971922945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238051193660293802629230593 178538395245220351971922945)
          ·
            refine ⟨133903796433915263978942209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178538395245220351971922945 133903796433915263978942209)
            ·
              refine ⟨100427847325436447984206657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133903796433915263978942209 100427847325436447984206657)
              ·
                refine ⟨75320885494077335988154993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100427847325436447984206657 75320885494077335988154993)
                ·
                  refine ⟨56490664120558001991116245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75320885494077335988154993 56490664120558001991116245)
                  ·
                    refine ⟨1323999940325578171666787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56490664120558001991116245 1323999940325578171666787)
                    ·
                      rfl

theorem cell22_3867721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_3867721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867721 prefixEnd_3867721 := by exact prefixLift 3867721
  have htrace : WordTrace (prefixWord ++ tailWord_3867721) baseStart_3867721 baseEnd_3867721 := by
    simpa [prefixWord, tailWord_3867721, baseEnd_3867721] using wordTrace_append hprefix tailTrace_3867721
  have hstable : (prefixWord ++ tailWord_3867721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867721).length < 2 ^ (prefixWord ++ tailWord_3867721).sum := by decide
  have hdescent : baseEnd_3867721 < baseStart_3867721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867768 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_3867768 : Nat := 118140960795 + 3867768 * 2 ^ 59
def prefixEnd_3867768 : Nat := 4983230072969 + 3 ^ 40 * 3867768 * 2
def baseEnd_3867768 : Nat := 441338676462028571913881

theorem tailTrace_3867768 : CollatzResearch.WordTrace tailWord_3867768 prefixEnd_3867768 441338676462028571913881 := by
  unfold tailWord_3867768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70534544125872286514733979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94046058834496382019645305 70534544125872286514733979)
  ·
    refine ⟨105801816188808429772100969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70534544125872286514733979 105801816188808429772100969)
    ·
      refine ⟨79351362141606322329075727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105801816188808429772100969 79351362141606322329075727)
      ·
        refine ⟨119027043212409483493613591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79351362141606322329075727 119027043212409483493613591)
        ·
          refine ⟨178540564818614225240420387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119027043212409483493613591 178540564818614225240420387)
          ·
            refine ⟨267810847227921337860630581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178540564818614225240420387 267810847227921337860630581)
            ·
              refine ⟨25107266927617625424434117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267810847227921337860630581 25107266927617625424434117)
              ·
                refine ⟨4707612548928304767081397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25107266927617625424434117 4707612548928304767081397)
                ·
                  refine ⟨441338676462028571913881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707612548928304767081397 441338676462028571913881)
                  ·
                    rfl

theorem cell22_3867768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_3867768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867768 prefixEnd_3867768 := by exact prefixLift 3867768
  have htrace : WordTrace (prefixWord ++ tailWord_3867768) baseStart_3867768 baseEnd_3867768 := by
    simpa [prefixWord, tailWord_3867768, baseEnd_3867768] using wordTrace_append hprefix tailTrace_3867768
  have hstable : (prefixWord ++ tailWord_3867768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867768).length < 2 ^ (prefixWord ++ tailWord_3867768).sum := by decide
  have hdescent : baseEnd_3867768 < baseStart_3867768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867772 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_3867772 : Nat := 118140960795 + 3867772 * 2 ^ 59
def prefixEnd_3867772 : Nat := 4983230072969 + 3 ^ 40 * 3867772 * 2
def baseEnd_3867772 : Nat := 1324017398667831038641631

theorem tailTrace_3867772 : CollatzResearch.WordTrace tailWord_3867772 prefixEnd_3867772 1324017398667831038641631 := by
  unfold tailWord_3867772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70534617071865040856306785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94046156095820054475075713 70534617071865040856306785)
  ·
    refine ⟨52900962803898780642230089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70534617071865040856306785 52900962803898780642230089)
    ·
      refine ⟨39675722102924085481672567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52900962803898780642230089 39675722102924085481672567)
      ·
        refine ⟨59513583154386128222508851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39675722102924085481672567 59513583154386128222508851)
        ·
          refine ⟨89270374731579192333763277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59513583154386128222508851 89270374731579192333763277)
          ·
            refine ⟨33476390524342197125161229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89270374731579192333763277 33476390524342197125161229)
            ·
              refine ⟨12553646446628323921935461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33476390524342197125161229 12553646446628323921935461)
              ·
                refine ⟨2353808708742810735362899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12553646446628323921935461 2353808708742810735362899)
                ·
                  refine ⟨3530713063114216103044349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353808708742810735362899 3530713063114216103044349)
                  ·
                    refine ⟨1324017398667831038641631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530713063114216103044349 1324017398667831038641631)
                    ·
                      rfl

theorem cell22_3867772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_3867772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867772 prefixEnd_3867772 := by exact prefixLift 3867772
  have htrace : WordTrace (prefixWord ++ tailWord_3867772) baseStart_3867772 baseEnd_3867772 := by
    simpa [prefixWord, tailWord_3867772, baseEnd_3867772] using wordTrace_append hprefix tailTrace_3867772
  have hstable : (prefixWord ++ tailWord_3867772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867772).length < 2 ^ (prefixWord ++ tailWord_3867772).sum := by decide
  have hdescent : baseEnd_3867772 < baseStart_3867772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867806 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3867806 : Nat := 118140960795 + 3867806 * 2 ^ 59
def prefixEnd_3867806 : Nat := 4983230072969 + 3 ^ 40 * 3867806 * 2
def baseEnd_3867806 : Nat := 1324029037562666283291527

theorem tailTrace_3867806 : CollatzResearch.WordTrace tailWord_3867806 prefixEnd_3867806 1324029037562666283291527 := by
  unfold tailWord_3867806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17633809278200863189918909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94046982817071270346234181 17633809278200863189918909)
  ·
    refine ⟨6612678479325323696219591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17633809278200863189918909 6612678479325323696219591)
    ·
      refine ⟨9919017718987985544329387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6612678479325323696219591 9919017718987985544329387)
      ·
        refine ⟨14878526578481978316494081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919017718987985544329387 14878526578481978316494081)
        ·
          refine ⟨11158894933861483737370561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14878526578481978316494081 11158894933861483737370561)
          ·
            refine ⟨8369171200396112803027921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11158894933861483737370561 8369171200396112803027921)
            ·
              refine ⟨6276878400297084602270941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8369171200396112803027921 6276878400297084602270941)
              ·
                refine ⟨2353829400111406725851603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6276878400297084602270941 2353829400111406725851603)
                ·
                  refine ⟨3530744100167110088777405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353829400111406725851603 3530744100167110088777405)
                  ·
                    refine ⟨1324029037562666283291527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530744100167110088777405 1324029037562666283291527)
                    ·
                      rfl

theorem cell22_3867806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3867806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867806 prefixEnd_3867806 := by exact prefixLift 3867806
  have htrace : WordTrace (prefixWord ++ tailWord_3867806) baseStart_3867806 baseEnd_3867806 := by
    simpa [prefixWord, tailWord_3867806, baseEnd_3867806] using wordTrace_append hprefix tailTrace_3867806
  have hstable : (prefixWord ++ tailWord_3867806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867806).length < 2 ^ (prefixWord ++ tailWord_3867806).sum := by decide
  have hdescent : baseEnd_3867806 < baseStart_3867806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867843 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 6, 4]
def baseStart_3867843 : Nat := 118140960795 + 3867843 * 2 ^ 59
def prefixEnd_3867843 : Nat := 4983230072969 + 3 ^ 40 * 3867843 * 2
def baseEnd_3867843 : Nat := 1324041703418810520116413

theorem tailTrace_3867843 : CollatzResearch.WordTrace tailWord_3867843 prefixEnd_3867843 1324041703418810520116413 := by
  unfold tailWord_3867843
  simp only [CollatzResearch.WordTrace]
  refine ⟨141071823726472860838448183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94047882484315240558965455 141071823726472860838448183)
  ·
    refine ⟨211607735589709291257672275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141071823726472860838448183 211607735589709291257672275)
    ·
      refine ⟨317411603384563936886508413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211607735589709291257672275 317411603384563936886508413)
      ·
        refine ⟨119029351269211476332440655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317411603384563936886508413 119029351269211476332440655)
        ·
          refine ⟨178544026903817214498660983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119029351269211476332440655 178544026903817214498660983)
          ·
            refine ⟨267816040355725821747991475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178544026903817214498660983 267816040355725821747991475)
            ·
              refine ⟨401724060533588732621987213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267816040355725821747991475 401724060533588732621987213)
              ·
                refine ⟨150646522700095774733245205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401724060533588732621987213 150646522700095774733245205)
                ·
                  refine ⟨7061555751566989440620869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150646522700095774733245205 7061555751566989440620869)
                  ·
                    refine ⟨1324041703418810520116413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7061555751566989440620869 1324041703418810520116413)
                    ·
                      rfl

theorem cell22_3867843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_3867843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867843 prefixEnd_3867843 := by exact prefixLift 3867843
  have htrace : WordTrace (prefixWord ++ tailWord_3867843) baseStart_3867843 baseEnd_3867843 := by
    simpa [prefixWord, tailWord_3867843, baseEnd_3867843] using wordTrace_append hprefix tailTrace_3867843
  have hstable : (prefixWord ++ tailWord_3867843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867843).length < 2 ^ (prefixWord ++ tailWord_3867843).sum := by decide
  have hdescent : baseEnd_3867843 < baseStart_3867843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867864 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 4]
def baseStart_3867864 : Nat := 118140960795 + 3867864 * 2 ^ 59
def prefixEnd_3867864 : Nat := 4983230072969 + 3 ^ 40 * 3867864 * 2
def baseEnd_3867864 : Nat := 441349630715991155113783

theorem tailTrace_3867864 : CollatzResearch.WordTrace tailWord_3867864 prefixEnd_3867864 441349630715991155113783 := by
  unfold tailWord_3867864
  simp only [CollatzResearch.WordTrace]
  refine ⟨70536294829698390712481323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94048393106264520949975097 70536294829698390712481323)
  ·
    refine ⟨105804442244547586068721985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70536294829698390712481323 105804442244547586068721985)
    ·
      refine ⟨79353331683410689551541489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105804442244547586068721985 79353331683410689551541489)
      ·
        refine ⟨59514998762558017163656117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79353331683410689551541489 59514998762558017163656117)
        ·
          refine ⟨5579531133989814109092761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59514998762558017163656117 5579531133989814109092761)
          ·
            refine ⟨4184648350492360581819571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5579531133989814109092761 4184648350492360581819571)
            ·
              refine ⟨6276972525738540872729357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184648350492360581819571 6276972525738540872729357)
              ·
                refine ⟨2353864697151952827273509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6276972525738540872729357 2353864697151952827273509)
                ·
                  refine ⟨441349630715991155113783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353864697151952827273509 441349630715991155113783)
                  ·
                    rfl

theorem cell22_3867864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_3867864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867864 prefixEnd_3867864 := by exact prefixLift 3867864
  have htrace : WordTrace (prefixWord ++ tailWord_3867864) baseStart_3867864 baseEnd_3867864 := by
    simpa [prefixWord, tailWord_3867864, baseEnd_3867864] using wordTrace_append hprefix tailTrace_3867864
  have hstable : (prefixWord ++ tailWord_3867864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867864).length < 2 ^ (prefixWord ++ tailWord_3867864).sum := by decide
  have hdescent : baseEnd_3867864 < baseStart_3867864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867877 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3867877 : Nat := 118140960795 + 3867877 * 2 ^ 59
def prefixEnd_3867877 : Nat := 4983230072969 + 3 ^ 40 * 3867877 * 2
def baseEnd_3867877 : Nat := 1324053342313645764766309

theorem tailTrace_3867877 : CollatzResearch.WordTrace tailWord_3867877 prefixEnd_3867877 1324053342313645764766309 := by
  unfold tailWord_3867877
  simp only [CollatzResearch.WordTrace]
  refine ⟨141073063808349684645185885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94048709205566456430123923 141073063808349684645185885)
  ·
    refine ⟨52902398928131131741944707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141073063808349684645185885 52902398928131131741944707)
    ·
      refine ⟨79353598392196697612917061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52902398928131131741944707 79353598392196697612917061)
      ·
        refine ⟨14878799698536880802421949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79353598392196697612917061 14878799698536880802421949)
        ·
          refine ⟨5579549886951330300908231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14878799698536880802421949 5579549886951330300908231)
          ·
            refine ⟨8369324830426995451362347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579549886951330300908231 8369324830426995451362347)
            ·
              refine ⟨12553987245640493177043521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369324830426995451362347 12553987245640493177043521)
              ·
                refine ⟨9415490434230369882782641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12553987245640493177043521 9415490434230369882782641)
                ·
                  refine ⟨7061617825672777412086981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9415490434230369882782641 7061617825672777412086981)
                  ·
                    refine ⟨1324053342313645764766309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7061617825672777412086981 1324053342313645764766309)
                    ·
                      rfl

theorem cell22_3867877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3867877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867877 prefixEnd_3867877 := by exact prefixLift 3867877
  have htrace : WordTrace (prefixWord ++ tailWord_3867877) baseStart_3867877 baseEnd_3867877 := by
    simpa [prefixWord, tailWord_3867877, baseEnd_3867877] using wordTrace_append hprefix tailTrace_3867877
  have hstable : (prefixWord ++ tailWord_3867877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867877).length < 2 ^ (prefixWord ++ tailWord_3867877).sum := by decide
  have hdescent : baseEnd_3867877 < baseStart_3867877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867941 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_3867941 : Nat := 118140960795 + 3867941 * 2 ^ 59
def prefixEnd_3867941 : Nat := 4983230072969 + 3 ^ 40 * 3867941 * 2
def baseEnd_3867941 : Nat := 1324075250821570931166113

theorem tailTrace_3867941 : CollatzResearch.WordTrace tailWord_3867941 prefixEnd_3867941 1324075250821570931166113 := by
  unfold tailWord_3867941
  simp only [CollatzResearch.WordTrace]
  refine ⟨141075398080117823575515677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94050265386745215717010451 141075398080117823575515677)
  ·
    refine ⟨52903274280044183840818379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141075398080117823575515677 52903274280044183840818379)
    ·
      refine ⟨79354911420066275761227569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52903274280044183840818379 79354911420066275761227569)
      ·
        refine ⟨59516183565049706820920677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79354911420066275761227569 59516183565049706820920677)
        ·
          refine ⟨11159284418446820028922627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59516183565049706820920677 11159284418446820028922627)
          ·
            refine ⟨16738926627670230043383941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159284418446820028922627 16738926627670230043383941)
            ·
              refine ⟨3138548742688168133134489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16738926627670230043383941 3138548742688168133134489)
              ·
                refine ⟨2353911557016126099850867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3138548742688168133134489 2353911557016126099850867)
                ·
                  refine ⟨3530867335524189149776301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353911557016126099850867 3530867335524189149776301)
                  ·
                    refine ⟨1324075250821570931166113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530867335524189149776301 1324075250821570931166113)
                    ·
                      rfl

theorem cell22_3867941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_3867941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3867941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3867941 prefixEnd_3867941 := by exact prefixLift 3867941
  have htrace : WordTrace (prefixWord ++ tailWord_3867941) baseStart_3867941 baseEnd_3867941 := by
    simpa [prefixWord, tailWord_3867941, baseEnd_3867941] using wordTrace_append hprefix tailTrace_3867941
  have hstable : (prefixWord ++ tailWord_3867941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867941).length < 2 ^ (prefixWord ++ tailWord_3867941).sum := by decide
  have hdescent : baseEnd_3867941 < baseStart_3867941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868033 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 4]
def baseStart_3868033 : Nat := 118140960795 + 3868033 * 2 ^ 59
def prefixEnd_3868033 : Nat := 4983230072969 + 3 ^ 40 * 3868033 * 2
def baseEnd_3868033 : Nat := 441368914767237785955277

theorem tailTrace_3868033 : CollatzResearch.WordTrace tailWord_3868033 prefixEnd_3868033 441368914767237785955277 := by
  unfold tailWord_3868033
  simp only [CollatzResearch.WordTrace]
  refine ⟨141078753595784523287864753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94052502397189682191909835 141078753595784523287864753)
  ·
    refine ⟨105809065196838392465898565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141078753595784523287864753 105809065196838392465898565)
    ·
      refine ⟨19839199724407198587355981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105809065196838392465898565 19839199724407198587355981)
      ·
        refine ⟨7439699896652699470258493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19839199724407198587355981 7439699896652699470258493)
        ·
          refine ⟨2789887461244762301346935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7439699896652699470258493 2789887461244762301346935)
          ·
            refine ⟨4184831191867143452020403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789887461244762301346935 4184831191867143452020403)
            ·
              refine ⟨6277246787800715178030605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184831191867143452020403 6277246787800715178030605)
              ·
                refine ⟨2353967545425268191761477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6277246787800715178030605 2353967545425268191761477)
                ·
                  refine ⟨441368914767237785955277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353967545425268191761477 441368914767237785955277)
                  ·
                    rfl

theorem cell22_3868033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_3868033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868033 prefixEnd_3868033 := by exact prefixLift 3868033
  have htrace : WordTrace (prefixWord ++ tailWord_3868033) baseStart_3868033 baseEnd_3868033 := by
    simpa [prefixWord, tailWord_3868033, baseEnd_3868033] using wordTrace_append hprefix tailTrace_3868033
  have hstable : (prefixWord ++ tailWord_3868033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868033).length < 2 ^ (prefixWord ++ tailWord_3868033).sum := by decide
  have hdescent : baseEnd_3868033 < baseStart_3868033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868117 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 6]
def baseStart_3868117 : Nat := 118140960795 + 3868117 * 2 ^ 59
def prefixEnd_3868117 : Nat := 4983230072969 + 3 ^ 40 * 3868117 * 2
def baseEnd_3868117 : Nat := 441378499739455046255191

theorem tailTrace_3868117 : CollatzResearch.WordTrace tailWord_3868117 prefixEnd_3868117 441378499739455046255191 := by
  unfold tailWord_3868117
  simp only [CollatzResearch.WordTrace]
  refine ⟨141081817327480205633922605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94054544884986803755948403 141081817327480205633922605)
  ·
    refine ⟨52905681497805077112720977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141081817327480205633922605 52905681497805077112720977)
    ·
      refine ⟨39679261123353807834540733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52905681497805077112720977 39679261123353807834540733)
      ·
        refine ⟨14879722921257677937952775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39679261123353807834540733 14879722921257677937952775)
        ·
          refine ⟨22319584381886516906929163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14879722921257677937952775 22319584381886516906929163)
          ·
            refine ⟨33479376572829775360393745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22319584381886516906929163 33479376572829775360393745)
            ·
              refine ⟨25109532429622331520295309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33479376572829775360393745 25109532429622331520295309)
              ·
                refine ⟨9416074661108374320110741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25109532429622331520295309 9416074661108374320110741)
                ·
                  refine ⟨441378499739455046255191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9416074661108374320110741 441378499739455046255191)
                  ·
                    rfl

theorem cell22_3868117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_3868117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868117 prefixEnd_3868117 := by exact prefixLift 3868117
  have htrace : WordTrace (prefixWord ++ tailWord_3868117) baseStart_3868117 baseEnd_3868117 := by
    simpa [prefixWord, tailWord_3868117, baseEnd_3868117] using wordTrace_append hprefix tailTrace_3868117
  have hstable : (prefixWord ++ tailWord_3868117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868117).length < 2 ^ (prefixWord ++ tailWord_3868117).sum := by decide
  have hdescent : baseEnd_3868117 < baseStart_3868117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868147 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 2, 4]
def baseStart_3868147 : Nat := 118140960795 + 3868147 * 2 ^ 59
def prefixEnd_3868147 : Nat := 4983230072969 + 3 ^ 40 * 3868147 * 2
def baseEnd_3868147 : Nat := 1324145768831455060515481

theorem tailTrace_3868147 : CollatzResearch.WordTrace tailWord_3868147 prefixEnd_3868147 1324145768831455060515481 := by
  unfold tailWord_3868147
  simp only [CollatzResearch.WordTrace]
  refine ⟨141082911517371520757514695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94055274344914347171676463 141082911517371520757514695)
  ·
    refine ⟨211624367276057281136272043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141082911517371520757514695 211624367276057281136272043)
    ·
      refine ⟨317436550914085921704408065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211624367276057281136272043 317436550914085921704408065)
      ·
        refine ⟨238077413185564441278306049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317436550914085921704408065 238077413185564441278306049)
        ·
          refine ⟨178558059889173330958729537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238077413185564441278306049 178558059889173330958729537)
          ·
            refine ⟨133918544916879998219047153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178558059889173330958729537 133918544916879998219047153)
            ·
              refine ⟨100438908687659998664285365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133918544916879998219047153 100438908687659998664285365)
              ·
                refine ⟨9416147689468124874776753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100438908687659998664285365 9416147689468124874776753)
                ·
                  refine ⟨7062110767101093656082565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416147689468124874776753 7062110767101093656082565)
                  ·
                    refine ⟨1324145768831455060515481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062110767101093656082565 1324145768831455060515481)
                    ·
                      rfl

theorem cell22_3868147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_3868147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868147 prefixEnd_3868147 := by exact prefixLift 3868147
  have htrace : WordTrace (prefixWord ++ tailWord_3868147) baseStart_3868147 baseEnd_3868147 := by
    simpa [prefixWord, tailWord_3868147, baseEnd_3868147] using wordTrace_append hprefix tailTrace_3868147
  have hstable : (prefixWord ++ tailWord_3868147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868147).length < 2 ^ (prefixWord ++ tailWord_3868147).sum := by decide
  have hdescent : baseEnd_3868147 < baseStart_3868147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868316 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3868316 : Nat := 118140960795 + 3868316 * 2 ^ 59
def prefixEnd_3868316 : Nat := 4983230072969 + 3 ^ 40 * 3868316 * 2
def baseEnd_3868316 : Nat := 1324203620985194953039963

theorem tailTrace_3868316 : CollatzResearch.WordTrace tailWord_3868316 prefixEnd_3868316 1324203620985194953039963 := by
  unfold tailWord_3868316
  simp only [CollatzResearch.WordTrace]
  refine ⟨70544537726879631310208401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94059383635839508413611201 70544537726879631310208401)
  ·
    refine ⟨52908403295159723482656301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70544537726879631310208401 52908403295159723482656301)
    ·
      refine ⟨19840651235684896305996113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52908403295159723482656301 19840651235684896305996113)
      ·
        refine ⟨14880488426763672229497085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19840651235684896305996113 14880488426763672229497085)
        ·
          refine ⟨5580183160036377086061407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14880488426763672229497085 5580183160036377086061407)
          ·
            refine ⟨8370274740054565629092111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580183160036377086061407 8370274740054565629092111)
            ·
              refine ⟨12555412110081848443638167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370274740054565629092111 12555412110081848443638167)
              ·
                refine ⟨18833118165122772665457251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555412110081848443638167 18833118165122772665457251)
                ·
                  refine ⟨28249677247684158998185877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18833118165122772665457251 28249677247684158998185877)
                  ·
                    refine ⟨1324203620985194953039963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28249677247684158998185877 1324203620985194953039963)
                    ·
                      rfl

theorem cell22_3868316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3868316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868316 prefixEnd_3868316 := by exact prefixLift 3868316
  have htrace : WordTrace (prefixWord ++ tailWord_3868316) baseStart_3868316 baseEnd_3868316 := by
    simpa [prefixWord, tailWord_3868316, baseEnd_3868316] using wordTrace_append hprefix tailTrace_3868316
  have hstable : (prefixWord ++ tailWord_3868316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868316).length < 2 ^ (prefixWord ++ tailWord_3868316).sum := by decide
  have hdescent : baseEnd_3868316 < baseStart_3868316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868322 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3868322 : Nat := 118140960795 + 3868322 * 2 ^ 59
def prefixEnd_3868322 : Nat := 4983230072969 + 3 ^ 40 * 3868322 * 2
def baseEnd_3868322 : Nat := 1324205674907812937389945

theorem tailTrace_3868322 : CollatzResearch.WordTrace tailWord_3868322 prefixEnd_3868322 1324205674907812937389945 := by
  unfold tailWord_3868322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35272323572934381411283805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94059529527825017096756813 35272323572934381411283805)
  ·
    refine ⟨13227121339850393029231427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35272323572934381411283805 13227121339850393029231427)
    ·
      refine ⟨19840682009775589543847141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13227121339850393029231427 19840682009775589543847141)
      ·
        refine ⟨3720127876832923039471339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19840682009775589543847141 3720127876832923039471339)
        ·
          refine ⟨5580191815249384559207009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720127876832923039471339 5580191815249384559207009)
          ·
            refine ⟨4185143861437038419405257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580191815249384559207009 4185143861437038419405257)
            ·
              refine ⟨3138857896077778814553943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185143861437038419405257 3138857896077778814553943)
              ·
                refine ⟨4708286844116668221830915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138857896077778814553943 4708286844116668221830915)
                ·
                  refine ⟨7062430266175002332746373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708286844116668221830915 7062430266175002332746373)
                  ·
                    refine ⟨1324205674907812937389945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062430266175002332746373 1324205674907812937389945)
                    ·
                      rfl

theorem cell22_3868322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3868322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868322 prefixEnd_3868322 := by exact prefixLift 3868322
  have htrace : WordTrace (prefixWord ++ tailWord_3868322) baseStart_3868322 baseEnd_3868322 := by
    simpa [prefixWord, tailWord_3868322, baseEnd_3868322] using wordTrace_append hprefix tailTrace_3868322
  have hstable : (prefixWord ++ tailWord_3868322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868322).length < 2 ^ (prefixWord ++ tailWord_3868322).sum := by decide
  have hdescent : baseEnd_3868322 < baseStart_3868322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868346 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_3868346 : Nat := 118140960795 + 3868346 * 2 ^ 59
def prefixEnd_3868346 : Nat := 4983230072969 + 3 ^ 40 * 3868346 * 2
def baseEnd_3868346 : Nat := 1324213890598284874789871

theorem tailTrace_3868346 : CollatzResearch.WordTrace tailWord_3868346 prefixEnd_3868346 1324213890598284874789871 := by
  unfold tailWord_3868346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35272542410912644436002223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94060113095767051829339261 35272542410912644436002223)
  ·
    refine ⟨52908813616368966654003335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35272542410912644436002223 52908813616368966654003335)
    ·
      refine ⟨79363220424553449981005003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52908813616368966654003335 79363220424553449981005003)
      ·
        refine ⟨119044830636830174971507505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79363220424553449981005003 119044830636830174971507505)
        ·
          refine ⟨89283622977622631228630629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119044830636830174971507505 89283622977622631228630629)
          ·
            refine ⟨16740679308304243355368243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89283622977622631228630629 16740679308304243355368243)
            ·
              refine ⟨25111018962456365033052365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16740679308304243355368243 25111018962456365033052365)
              ·
                refine ⟨9416632110921136887394637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25111018962456365033052365 9416632110921136887394637)
                ·
                  refine ⟨3531237041595426332772989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9416632110921136887394637 3531237041595426332772989)
                  ·
                    refine ⟨1324213890598284874789871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531237041595426332772989 1324213890598284874789871)
                    ·
                      rfl

theorem cell22_3868346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_3868346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868346 prefixEnd_3868346 := by exact prefixLift 3868346
  have htrace : WordTrace (prefixWord ++ tailWord_3868346) baseStart_3868346 baseEnd_3868346 := by
    simpa [prefixWord, tailWord_3868346, baseEnd_3868346] using wordTrace_append hprefix tailTrace_3868346
  have hstable : (prefixWord ++ tailWord_3868346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868346).length < 2 ^ (prefixWord ++ tailWord_3868346).sum := by decide
  have hdescent : baseEnd_3868346 < baseStart_3868346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868365 : List Nat := [1, 6, 2, 1, 1, 3, 2, 6]
def baseStart_3868365 : Nat := 118140960795 + 3868365 * 2 ^ 59
def prefixEnd_3868365 : Nat := 4983230072969 + 3 ^ 40 * 3868365 * 2
def baseEnd_3868365 : Nat := 147135599409619462062757

theorem tailTrace_3868365 : CollatzResearch.WordTrace tailWord_3868365 prefixEnd_3868365 147135599409619462062757 := by
  unfold tailWord_3868365
  simp only [CollatzResearch.WordTrace]
  refine ⟨141090862630581743988950549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94060575087054495992633699 141090862630581743988950549)
  ·
    refine ⟨6613634185808519249482057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141090862630581743988950549 6613634185808519249482057)
    ·
      refine ⟨4960225639356389437111543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6613634185808519249482057 4960225639356389437111543)
      ·
        refine ⟨7440338459034584155667315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960225639356389437111543 7440338459034584155667315)
        ·
          refine ⟨11160507688551876233500973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440338459034584155667315 11160507688551876233500973)
          ·
            refine ⟨4185190383206953587562865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11160507688551876233500973 4185190383206953587562865)
            ·
              refine ⟨3138892787405215190672149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185190383206953587562865 3138892787405215190672149)
              ·
                refine ⟨147135599409619462062757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3138892787405215190672149 147135599409619462062757)
                ·
                  rfl

theorem cell22_3868365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 6].length) (baseStart_3868365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868365 prefixEnd_3868365 := by exact prefixLift 3868365
  have htrace : WordTrace (prefixWord ++ tailWord_3868365) baseStart_3868365 baseEnd_3868365 := by
    simpa [prefixWord, tailWord_3868365, baseEnd_3868365] using wordTrace_append hprefix tailTrace_3868365
  have hstable : (prefixWord ++ tailWord_3868365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868365).length < 2 ^ (prefixWord ++ tailWord_3868365).sum := by decide
  have hdescent : baseEnd_3868365 < baseStart_3868365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868397 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_3868397 : Nat := 118140960795 + 3868397 * 2 ^ 59
def prefixEnd_3868397 : Nat := 4983230072969 + 3 ^ 40 * 3868397 * 2
def baseEnd_3868397 : Nat := 1324231348940537741764715

theorem tailTrace_3868397 : CollatzResearch.WordTrace tailWord_3868397 prefixEnd_3868397 1324231348940537741764715 := by
  unfold tailWord_3868397
  simp only [CollatzResearch.WordTrace]
  refine ⟨141092029766465813454115445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94061353177643875636076963 141092029766465813454115445)
  ·
    refine ⟨13227377790606170011323323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141092029766465813454115445 13227377790606170011323323)
    ·
      refine ⟨19841066685909255016984985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13227377790606170011323323 19841066685909255016984985)
      ·
        refine ⟨14880800014431941262738739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19841066685909255016984985 14880800014431941262738739)
        ·
          refine ⟨22321200021647911894108109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14880800014431941262738739 22321200021647911894108109)
          ·
            refine ⟨8370450008117966960290541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22321200021647911894108109 8370450008117966960290541)
            ·
              refine ⟨3138918753044237610108953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8370450008117966960290541 3138918753044237610108953)
              ·
                refine ⟨2354189064783178207581715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3138918753044237610108953 2354189064783178207581715)
                ·
                  refine ⟨3531283597174767311372573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354189064783178207581715 3531283597174767311372573)
                  ·
                    refine ⟨1324231348940537741764715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531283597174767311372573 1324231348940537741764715)
                    ·
                      rfl

theorem cell22_3868397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_3868397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868397 prefixEnd_3868397 := by exact prefixLift 3868397
  have htrace : WordTrace (prefixWord ++ tailWord_3868397) baseStart_3868397 baseEnd_3868397 := by
    simpa [prefixWord, tailWord_3868397, baseEnd_3868397] using wordTrace_append hprefix tailTrace_3868397
  have hstable : (prefixWord ++ tailWord_3868397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868397).length < 2 ^ (prefixWord ++ tailWord_3868397).sum := by decide
  have hdescent : baseEnd_3868397 < baseStart_3868397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868423 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3868423 : Nat := 118140960795 + 3868423 * 2 ^ 59
def prefixEnd_3868423 : Nat := 4983230072969 + 3 ^ 40 * 3868423 * 2
def baseEnd_3868423 : Nat := 1324240249271882340614635

theorem tailTrace_3868423 : CollatzResearch.WordTrace tailWord_3868423 prefixEnd_3868423 1324240249271882340614635 := by
  unfold tailWord_3868423
  simp only [CollatzResearch.WordTrace]
  refine ⟨141092978064371619894561923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94061985376247746596374615 141092978064371619894561923)
  ·
    refine ⟨211639467096557429841842885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141092978064371619894561923 211639467096557429841842885)
    ·
      refine ⟨39682400080604518095345541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211639467096557429841842885 39682400080604518095345541)
      ·
        refine ⟨7440450015113347142877289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39682400080604518095345541 7440450015113347142877289)
        ·
          refine ⟨5580337511335010357157967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7440450015113347142877289 5580337511335010357157967)
          ·
            refine ⟨8370506267002515535736951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580337511335010357157967 8370506267002515535736951)
            ·
              refine ⟨12555759400503773303605427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370506267002515535736951 12555759400503773303605427)
              ·
                refine ⟨18833639100755659955408141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555759400503773303605427 18833639100755659955408141)
                ·
                  refine ⟨7062614662783372483278053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18833639100755659955408141 7062614662783372483278053)
                  ·
                    refine ⟨1324240249271882340614635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062614662783372483278053 1324240249271882340614635)
                    ·
                      rfl

theorem cell22_3868423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3868423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868423 prefixEnd_3868423 := by exact prefixLift 3868423
  have htrace : WordTrace (prefixWord ++ tailWord_3868423) baseStart_3868423 baseEnd_3868423 := by
    simpa [prefixWord, tailWord_3868423, baseEnd_3868423] using wordTrace_append hprefix tailTrace_3868423
  have hstable : (prefixWord ++ tailWord_3868423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868423).length < 2 ^ (prefixWord ++ tailWord_3868423).sum := by decide
  have hdescent : baseEnd_3868423 < baseStart_3868423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868449 : List Nat := [1, 2, 3, 2, 1, 13]
def baseStart_3868449 : Nat := 118140960795 + 3868449 * 2 ^ 59
def prefixEnd_3868449 : Nat := 4983230072969 + 3 ^ 40 * 3868449 * 2
def baseEnd_3868449 : Nat := 16348754933373172092155

theorem tailTrace_3868449 : CollatzResearch.WordTrace tailWord_3868449 prefixEnd_3868449 16348754933373172092155 := by
  unfold tailWord_3868449
  simp only [CollatzResearch.WordTrace]
  refine ⟨141093926362277426335008401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94062617574851617556672267 141093926362277426335008401)
  ·
    refine ⟨105820444771708069751256301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141093926362277426335008401 105820444771708069751256301)
    ·
      refine ⟨39682666789390526156721113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105820444771708069751256301 39682666789390526156721113)
      ·
        refine ⟨29762000092042894617540835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39682666789390526156721113 29762000092042894617540835)
        ·
          refine ⟨44643000138064341926311253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29762000092042894617540835 44643000138064341926311253)
          ·
            refine ⟨16348754933373172092155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 44643000138064341926311253 16348754933373172092155)
            ·
              rfl

theorem cell22_3868449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 13].length) (baseStart_3868449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868449 prefixEnd_3868449 := by exact prefixLift 3868449
  have htrace : WordTrace (prefixWord ++ tailWord_3868449) baseStart_3868449 baseEnd_3868449 := by
    simpa [prefixWord, tailWord_3868449, baseEnd_3868449] using wordTrace_append hprefix tailTrace_3868449
  have hstable : (prefixWord ++ tailWord_3868449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868449).length < 2 ^ (prefixWord ++ tailWord_3868449).sum := by decide
  have hdescent : baseEnd_3868449 < baseStart_3868449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868451 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 2, 4]
def baseStart_3868451 : Nat := 118140960795 + 3868451 * 2 ^ 59
def prefixEnd_3868451 : Nat := 4983230072969 + 3 ^ 40 * 3868451 * 2
def baseEnd_3868451 : Nat := 1324249834244099600914549

theorem tailTrace_3868451 : CollatzResearch.WordTrace tailWord_3868451 prefixEnd_3868451 1324249834244099600914549 := by
  unfold tailWord_3868451
  simp only [CollatzResearch.WordTrace]
  refine ⟨141093999308270180676581207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94062666205513453784387471 141093999308270180676581207)
  ·
    refine ⟨211640998962405271014871811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141093999308270180676581207 211640998962405271014871811)
    ·
      refine ⟨317461498443607906522307717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211640998962405271014871811 317461498443607906522307717)
      ·
        refine ⟨59524030958176482472932697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317461498443607906522307717 59524030958176482472932697)
        ·
          refine ⟨44643023218632361854699523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59524030958176482472932697 44643023218632361854699523)
          ·
            refine ⟨66964534827948542782049285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44643023218632361854699523 66964534827948542782049285)
            ·
              refine ⟨12555850280240351771634241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66964534827948542782049285 12555850280240351771634241)
              ·
                refine ⟨9416887710180263828725681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12555850280240351771634241 9416887710180263828725681)
                ·
                  refine ⟨7062665782635197871544261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416887710180263828725681 7062665782635197871544261)
                  ·
                    refine ⟨1324249834244099600914549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062665782635197871544261 1324249834244099600914549)
                    ·
                      rfl

theorem cell22_3868451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_3868451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868451 prefixEnd_3868451 := by exact prefixLift 3868451
  have htrace : WordTrace (prefixWord ++ tailWord_3868451) baseStart_3868451 baseEnd_3868451 := by
    simpa [prefixWord, tailWord_3868451, baseEnd_3868451] using wordTrace_append hprefix tailTrace_3868451
  have hstable : (prefixWord ++ tailWord_3868451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868451).length < 2 ^ (prefixWord ++ tailWord_3868451).sum := by decide
  have hdescent : baseEnd_3868451 < baseStart_3868451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868453 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_3868453 : Nat := 118140960795 + 3868453 * 2 ^ 59
def prefixEnd_3868453 : Nat := 4983230072969 + 3 ^ 40 * 3868453 * 2
def baseEnd_3868453 : Nat := 1324250518884972262364543

theorem tailTrace_3868453 : CollatzResearch.WordTrace tailWord_3868453 prefixEnd_3868453 1324250518884972262364543 := by
  unfold tailWord_3868453
  simp only [CollatzResearch.WordTrace]
  refine ⟨141094072254262935018154013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94062714836175290012102675 141094072254262935018154013)
  ·
    refine ⟨52910277095348600631807755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141094072254262935018154013 52910277095348600631807755)
    ·
      refine ⟨79365415643022900947711633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52910277095348600631807755 79365415643022900947711633)
      ·
        refine ⟨59524061732267175710783725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79365415643022900947711633 59524061732267175710783725)
        ·
          refine ⟨22321523149600190891543897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59524061732267175710783725 22321523149600190891543897)
          ·
            refine ⟨16741142362200143168657923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22321523149600190891543897 16741142362200143168657923)
            ·
              refine ⟨25111713543300214752986885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16741142362200143168657923 25111713543300214752986885)
              ·
                refine ⟨4708446289368790266185041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25111713543300214752986885 4708446289368790266185041)
                ·
                  refine ⟨3531334717026592699638781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708446289368790266185041 3531334717026592699638781)
                  ·
                    refine ⟨1324250518884972262364543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531334717026592699638781 1324250518884972262364543)
                    ·
                      rfl

theorem cell22_3868453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_3868453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868453 prefixEnd_3868453 := by exact prefixLift 3868453
  have htrace : WordTrace (prefixWord ++ tailWord_3868453) baseStart_3868453 baseEnd_3868453 := by
    simpa [prefixWord, tailWord_3868453, baseEnd_3868453] using wordTrace_append hprefix tailTrace_3868453
  have hstable : (prefixWord ++ tailWord_3868453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868453).length < 2 ^ (prefixWord ++ tailWord_3868453).sum := by decide
  have hdescent : baseEnd_3868453 < baseStart_3868453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868464 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_3868464 : Nat := 118140960795 + 3868464 * 2 ^ 59
def prefixEnd_3868464 : Nat := 4983230072969 + 3 ^ 40 * 3868464 * 2
def baseEnd_3868464 : Nat := 1324254284409771900339509

theorem tailTrace_3868464 : CollatzResearch.WordTrace tailWord_3868464 prefixEnd_3868464 1324254284409771900339509 := by
  unfold tailWord_3868464
  simp only [CollatzResearch.WordTrace]
  refine ⟨70547236728611541948402223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94062982304815389264536297 70547236728611541948402223)
  ·
    refine ⟨105820855092917312922603335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70547236728611541948402223 105820855092917312922603335)
    ·
      refine ⟨158731282639375969383905003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105820855092917312922603335 158731282639375969383905003)
      ·
        refine ⟨238096923959063954075857505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158731282639375969383905003 238096923959063954075857505)
        ·
          refine ⟨178572692969297965556893129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238096923959063954075857505 178572692969297965556893129)
          ·
            refine ⟨133929519726973474167669847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178572692969297965556893129 133929519726973474167669847)
            ·
              refine ⟨200894279590460211251504771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133929519726973474167669847 200894279590460211251504771)
              ·
                refine ⟨301341419385690316877257157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200894279590460211251504771 301341419385690316877257157)
                ·
                  refine ⟨56501516134816934414485717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301341419385690316877257157 56501516134816934414485717)
                  ·
                    refine ⟨1324254284409771900339509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56501516134816934414485717 1324254284409771900339509)
                    ·
                      rfl

theorem cell22_3868464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_3868464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868464 prefixEnd_3868464 := by exact prefixLift 3868464
  have htrace : WordTrace (prefixWord ++ tailWord_3868464) baseStart_3868464 baseEnd_3868464 := by
    simpa [prefixWord, tailWord_3868464, baseEnd_3868464] using wordTrace_append hprefix tailTrace_3868464
  have hstable : (prefixWord ++ tailWord_3868464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868464).length < 2 ^ (prefixWord ++ tailWord_3868464).sum := by decide
  have hdescent : baseEnd_3868464 < baseStart_3868464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868466 : List Nat := [3, 2, 1, 1, 3, 2, 3, 7]
def baseStart_3868466 : Nat := 118140960795 + 3868466 * 2 ^ 59
def prefixEnd_3868466 : Nat := 4983230072969 + 3 ^ 40 * 3868466 * 2
def baseEnd_3868466 : Nat := 147139441005627173532167

theorem tailTrace_3868466 : CollatzResearch.WordTrace tailWord_3868466 prefixEnd_3868466 147139441005627173532167 := by
  unfold tailWord_3868466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35273636600803959559594313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94063030935477225492251501 35273636600803959559594313)
  ·
    refine ⟨26455227450602969669695735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35273636600803959559594313 26455227450602969669695735)
    ·
      refine ⟨39682841175904454504543603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26455227450602969669695735 39682841175904454504543603)
      ·
        refine ⟨59524261763856681756815405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39682841175904454504543603 59524261763856681756815405)
        ·
          refine ⟨22321598161446255658805777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59524261763856681756815405 22321598161446255658805777)
          ·
            refine ⟨16741198621084691744104333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22321598161446255658805777 16741198621084691744104333)
            ·
              refine ⟨6277949482906759404039125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16741198621084691744104333 6277949482906759404039125)
              ·
                refine ⟨147139441005627173532167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6277949482906759404039125 147139441005627173532167)
                ·
                  rfl

theorem cell22_3868466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_3868466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868466 prefixEnd_3868466 := by exact prefixLift 3868466
  have htrace : WordTrace (prefixWord ++ tailWord_3868466) baseStart_3868466 baseEnd_3868466 := by
    simpa [prefixWord, tailWord_3868466, baseEnd_3868466] using wordTrace_append hprefix tailTrace_3868466
  have hstable : (prefixWord ++ tailWord_3868466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868466).length < 2 ^ (prefixWord ++ tailWord_3868466).sum := by decide
  have hdescent : baseEnd_3868466 < baseStart_3868466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868470 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3868470 : Nat := 118140960795 + 3868470 * 2 ^ 59
def prefixEnd_3868470 : Nat := 4983230072969 + 3 ^ 40 * 3868470 * 2
def baseEnd_3868470 : Nat := 1324256338332389884689491

theorem tailTrace_3868470 : CollatzResearch.WordTrace tailWord_3868470 prefixEnd_3868470 1324256338332389884689491 := by
  unfold tailWord_3868470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818418268450084182595179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94063128196800897947681909 8818418268450084182595179)
  ·
    refine ⟨13227627402675126273892769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8818418268450084182595179 13227627402675126273892769)
    ·
      refine ⟨9920720552006344705419577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227627402675126273892769 9920720552006344705419577)
      ·
        refine ⟨7440540414004758529064683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9920720552006344705419577 7440540414004758529064683)
        ·
          refine ⟨11160810621007137793597025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440540414004758529064683 11160810621007137793597025)
          ·
            refine ⟨8370607965755353345197769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11160810621007137793597025 8370607965755353345197769)
            ·
              refine ⟨6277955974316515008898327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8370607965755353345197769 6277955974316515008898327)
              ·
                refine ⟨9416933961474772513347491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277955974316515008898327 9416933961474772513347491)
                ·
                  refine ⟨14125400942212158770021237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9416933961474772513347491 14125400942212158770021237)
                  ·
                    refine ⟨1324256338332389884689491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14125400942212158770021237 1324256338332389884689491)
                    ·
                      rfl

theorem cell22_3868470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3868470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868470 prefixEnd_3868470 := by exact prefixLift 3868470
  have htrace : WordTrace (prefixWord ++ tailWord_3868470) baseStart_3868470 baseEnd_3868470 := by
    simpa [prefixWord, tailWord_3868470, baseEnd_3868470] using wordTrace_append hprefix tailTrace_3868470
  have hstable : (prefixWord ++ tailWord_3868470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868470).length < 2 ^ (prefixWord ++ tailWord_3868470).sum := by decide
  have hdescent : baseEnd_3868470 < baseStart_3868470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868511 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 7]
def baseStart_3868511 : Nat := 118140960795 + 3868511 * 2 ^ 59
def prefixEnd_3868511 : Nat := 4983230072969 + 3 ^ 40 * 3868511 * 2
def baseEnd_3868511 : Nat := 441423457823426481471455

theorem tailTrace_3868511 : CollatzResearch.WordTrace tailWord_3868511 prefixEnd_3868511 441423457823426481471455 := by
  unfold tailWord_3868511
  simp only [CollatzResearch.WordTrace]
  refine ⟨141096187688052810923765387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94064125125368540615843591 141096187688052810923765387)
  ·
    refine ⟨211644281532079216385648081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141096187688052810923765387 211644281532079216385648081)
    ·
      refine ⟨158733211149059412289236061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211644281532079216385648081 158733211149059412289236061)
      ·
        refine ⟨59524954180897279608463523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158733211149059412289236061 59524954180897279608463523)
        ·
          refine ⟨89287431271345919412695285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59524954180897279608463523 89287431271345919412695285)
          ·
            refine ⟨8370696681688679944940183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89287431271345919412695285 8370696681688679944940183)
            ·
              refine ⟨12556045022533019917410275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370696681688679944940183 12556045022533019917410275)
              ·
                refine ⟨18834067533799529876115413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556045022533019917410275 18834067533799529876115413)
                ·
                  refine ⟨441423457823426481471455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18834067533799529876115413 441423457823426481471455)
                  ·
                    rfl

theorem cell22_3868511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 7].length) (baseStart_3868511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868511 prefixEnd_3868511 := by exact prefixLift 3868511
  have htrace : WordTrace (prefixWord ++ tailWord_3868511) baseStart_3868511 baseEnd_3868511 := by
    simpa [prefixWord, tailWord_3868511, baseEnd_3868511] using wordTrace_append hprefix tailTrace_3868511
  have hstable : (prefixWord ++ tailWord_3868511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868511).length < 2 ^ (prefixWord ++ tailWord_3868511).sum := by decide
  have hdescent : baseEnd_3868511 < baseStart_3868511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868515 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 3, 3]
def baseStart_3868515 : Nat := 118140960795 + 3868515 * 2 ^ 59
def prefixEnd_3868515 : Nat := 4983230072969 + 3 ^ 40 * 3868515 * 2
def baseEnd_3868515 : Nat := 1324271742752024767314353

theorem tailTrace_3868515 : CollatzResearch.WordTrace tailWord_3868515 prefixEnd_3868515 1324271742752024767314353 := by
  unfold tailWord_3868515
  simp only [CollatzResearch.WordTrace]
  refine ⟨141096333580038319606910999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94064222386692213071273999 141096333580038319606910999)
  ·
    refine ⟨211644500370057479410366499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141096333580038319606910999 211644500370057479410366499)
    ·
      refine ⟨317466750555086219115549749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211644500370057479410366499 317466750555086219115549749)
      ·
        refine ⟨29762507864539333042082789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317466750555086219115549749 29762507864539333042082789)
        ·
          refine ⟨5580470224601124945390523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29762507864539333042082789 5580470224601124945390523)
          ·
            refine ⟨8370705336901687418085785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580470224601124945390523 8370705336901687418085785)
            ·
              refine ⟨6278029002676265563564339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8370705336901687418085785 6278029002676265563564339)
              ·
                refine ⟨9417043504014398345346509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278029002676265563564339 9417043504014398345346509)
                ·
                  refine ⟨3531391314005399379504941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9417043504014398345346509 3531391314005399379504941)
                  ·
                    refine ⟨1324271742752024767314353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531391314005399379504941 1324271742752024767314353)
                    ·
                      rfl

theorem cell22_3868515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 3].length) (baseStart_3868515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868515 prefixEnd_3868515 := by exact prefixLift 3868515
  have htrace : WordTrace (prefixWord ++ tailWord_3868515) baseStart_3868515 baseEnd_3868515 := by
    simpa [prefixWord, tailWord_3868515, baseEnd_3868515] using wordTrace_append hprefix tailTrace_3868515
  have hstable : (prefixWord ++ tailWord_3868515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868515).length < 2 ^ (prefixWord ++ tailWord_3868515).sum := by decide
  have hdescent : baseEnd_3868515 < baseStart_3868515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868566 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3868566 : Nat := 118140960795 + 3868566 * 2 ^ 59
def prefixEnd_3868566 : Nat := 4983230072969 + 3 ^ 40 * 3868566 * 2
def baseEnd_3868566 : Nat := 1324289201094277634289197

theorem tailTrace_3868566 : CollatzResearch.WordTrace tailWord_3868566 prefixEnd_3868566 1324289201094277634289197 := by
  unfold tailWord_3868566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818637106428347207313597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94065462468569036878011701 8818637106428347207313597)
  ·
    refine ⟨3306988914910630202742599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8818637106428347207313597 3306988914910630202742599)
    ·
      refine ⟨4960483372365945304113899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3306988914910630202742599 4960483372365945304113899)
      ·
        refine ⟨7440725058548917956170849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960483372365945304113899 7440725058548917956170849)
        ·
          refine ⟨5580543793911688467128137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7440725058548917956170849 5580543793911688467128137)
          ·
            refine ⟨4185407845433766350346103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580543793911688467128137 4185407845433766350346103)
            ·
              refine ⟨6278111768150649525519155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185407845433766350346103 6278111768150649525519155)
              ·
                refine ⟨9417167652225974288278733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278111768150649525519155 9417167652225974288278733)
                ·
                  refine ⟨3531437869584740358104525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9417167652225974288278733 3531437869584740358104525)
                  ·
                    refine ⟨1324289201094277634289197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531437869584740358104525 1324289201094277634289197)
                    ·
                      rfl

theorem cell22_3868566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3868566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868566 prefixEnd_3868566 := by exact prefixLift 3868566
  have htrace : WordTrace (prefixWord ++ tailWord_3868566) baseStart_3868566 baseEnd_3868566 := by
    simpa [prefixWord, tailWord_3868566, baseEnd_3868566] using wordTrace_append hprefix tailTrace_3868566
  have hstable : (prefixWord ++ tailWord_3868566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868566).length < 2 ^ (prefixWord ++ tailWord_3868566).sum := by decide
  have hdescent : baseEnd_3868566 < baseStart_3868566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868573 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 6]
def baseStart_3868573 : Nat := 118140960795 + 3868573 * 2 ^ 59
def prefixEnd_3868573 : Nat := 4983230072969 + 3 ^ 40 * 3868573 * 2
def baseEnd_3868573 : Nat := 441430532445777316454725

theorem tailTrace_3868573 : CollatzResearch.WordTrace tailWord_3868573 prefixEnd_3868573 441430532445777316454725 := by
  unfold tailWord_3868573
  simp only [CollatzResearch.WordTrace]
  refine ⟨141098449013828195512522373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94065632675885463675014915 141098449013828195512522373)
  ·
    refine ⟨26455959190092786658597945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141098449013828195512522373 26455959190092786658597945)
    ·
      refine ⟨19841969392569589993948459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26455959190092786658597945 19841969392569589993948459)
      ·
        refine ⟨29762954088854384990922689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19841969392569589993948459 29762954088854384990922689)
        ·
          refine ⟨22322215566640788743192017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29762954088854384990922689 22322215566640788743192017)
          ·
            refine ⟨16741661674980591557394013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22322215566640788743192017 16741661674980591557394013)
            ·
              refine ⟨6278123128117721834022755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16741661674980591557394013 6278123128117721834022755)
              ·
                refine ⟨9417184692176582751034133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278123128117721834022755 9417184692176582751034133)
                ·
                  refine ⟨441430532445777316454725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9417184692176582751034133 441430532445777316454725)
                  ·
                    rfl

theorem cell22_3868573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_3868573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868573 prefixEnd_3868573 := by exact prefixLift 3868573
  have htrace : WordTrace (prefixWord ++ tailWord_3868573) baseStart_3868573 baseEnd_3868573 := by
    simpa [prefixWord, tailWord_3868573, baseEnd_3868573] using wordTrace_append hprefix tailTrace_3868573
  have hstable : (prefixWord ++ tailWord_3868573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868573).length < 2 ^ (prefixWord ++ tailWord_3868573).sum := by decide
  have hdescent : baseEnd_3868573 < baseStart_3868573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868601 : List Nat := [1, 2, 1, 4, 2, 1, 1, 10]
def baseStart_3868601 : Nat := 118140960795 + 3868601 * 2 ^ 59
def prefixEnd_3868601 : Nat := 4983230072969 + 3 ^ 40 * 3868601 * 2
def baseEnd_3868601 : Nat := 147144575812172134407121

theorem tailTrace_3868601 : CollatzResearch.WordTrace tailWord_3868601 prefixEnd_3868601 147144575812172134407121 := by
  unfold tailWord_3868601
  simp only [CollatzResearch.WordTrace]
  refine ⟨141099470257726756294541657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94066313505151170863027771 141099470257726756294541657)
  ·
    refine ⟨105824602693295067220906243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141099470257726756294541657 105824602693295067220906243)
    ·
      refine ⟨158736904039942600831359365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105824602693295067220906243 158736904039942600831359365)
      ·
        refine ⟨29763169507489237655879881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158736904039942600831359365 29763169507489237655879881)
        ·
          refine ⟨22322377130616928241909911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29763169507489237655879881 22322377130616928241909911)
          ·
            refine ⟨33483565695925392362864867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22322377130616928241909911 33483565695925392362864867)
            ·
              refine ⟨50225348543888088544297301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33483565695925392362864867 50225348543888088544297301)
              ·
                refine ⟨147144575812172134407121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50225348543888088544297301 147144575812172134407121)
                ·
                  rfl

theorem cell22_3868601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 10].length) (baseStart_3868601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868601 prefixEnd_3868601 := by exact prefixLift 3868601
  have htrace : WordTrace (prefixWord ++ tailWord_3868601) baseStart_3868601 baseEnd_3868601 := by
    simpa [prefixWord, tailWord_3868601, baseEnd_3868601] using wordTrace_append hprefix tailTrace_3868601
  have hstable : (prefixWord ++ tailWord_3868601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868601).length < 2 ^ (prefixWord ++ tailWord_3868601).sum := by decide
  have hdescent : baseEnd_3868601 < baseStart_3868601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
