import V185TrunkScan19Chunk026

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_269946 : List Nat := [3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_269946 : Nat := 118140960795 + 269946 * 2 ^ 59
def prefixEnd_269946 : Nat := 4983230072969 + 3 ^ 40 * 269946 * 2
def baseEnd_269946 : Nat := 82140473338492485175435

theorem tailTrace_269946 : CollatzResearch.WordTrace tailWord_269946 prefixEnd_269946 82140473338492485175435 := by
  unfold tailWord_269946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461434870009804987863423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6563826320026146634302461 2461434870009804987863423)
  ·
    refine ⟨3692152305014707481795135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2461434870009804987863423 3692152305014707481795135)
    ·
      refine ⟨5538228457522061222692703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3692152305014707481795135 5538228457522061222692703)
      ·
        refine ⟨8307342686283091834039055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5538228457522061222692703 8307342686283091834039055)
        ·
          refine ⟨12461014029424637751058583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8307342686283091834039055 12461014029424637751058583)
          ·
            refine ⟨18691521044136956626587875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12461014029424637751058583 18691521044136956626587875)
            ·
              refine ⟨28037281566205434939881813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18691521044136956626587875 28037281566205434939881813)
              ·
                refine ⟨82140473338492485175435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28037281566205434939881813 82140473338492485175435)
                ·
                  rfl

theorem cell19_269946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_269946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269946 prefixEnd_269946 := by exact prefixLift 269946
  have htrace : WordTrace (prefixWord ++ tailWord_269946) baseStart_269946 baseEnd_269946 := by
    simpa [prefixWord, tailWord_269946, baseEnd_269946] using wordTrace_append hprefix tailTrace_269946
  have hstable : (prefixWord ++ tailWord_269946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269946).length < 2 ^ (prefixWord ++ tailWord_269946).sum := by decide
  have hdescent : baseEnd_269946 < baseStart_269946 := by decide
  rcases family_descends (prefixWord ++ tailWord_269946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269963 : List Nat := [1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_269963 : Nat := 118140960795 + 269963 * 2 ^ 59
def prefixEnd_269963 : Nat := 4983230072969 + 3 ^ 40 * 269963 * 2
def baseEnd_269963 : Nat := 82145646180641482797611

theorem tailTrace_269963 : CollatzResearch.WordTrace tailWord_269963 prefixEnd_269963 82145646180641482797611 := by
  unfold tailWord_269963
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846359520977631854822543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6564239680651754569881695 9846359520977631854822543)
  ·
    refine ⟨14769539281466447782233815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9846359520977631854822543 14769539281466447782233815)
    ·
      refine ⟨22154308922199671673350723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14769539281466447782233815 22154308922199671673350723)
      ·
        refine ⟨33231463383299507510026085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22154308922199671673350723 33231463383299507510026085)
        ·
          refine ⟨6230899384368657658129891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33231463383299507510026085 6230899384368657658129891)
          ·
            refine ⟨9346349076552986487194837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230899384368657658129891 9346349076552986487194837)
            ·
              refine ⟨219055056481710620793629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9346349076552986487194837 219055056481710620793629)
              ·
                refine ⟨82145646180641482797611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219055056481710620793629 82145646180641482797611)
                ·
                  rfl

theorem cell19_269963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_269963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269963 prefixEnd_269963 := by exact prefixLift 269963
  have htrace : WordTrace (prefixWord ++ tailWord_269963) baseStart_269963 baseEnd_269963 := by
    simpa [prefixWord, tailWord_269963, baseEnd_269963] using wordTrace_append hprefix tailTrace_269963
  have hstable : (prefixWord ++ tailWord_269963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269963).length < 2 ^ (prefixWord ++ tailWord_269963).sum := by decide
  have hdescent : baseEnd_269963 < baseStart_269963 := by decide
  rcases family_descends (prefixWord ++ tailWord_269963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270003 : List Nat := [1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_270003 : Nat := 118140960795 + 270003 * 2 ^ 59
def prefixEnd_270003 : Nat := 4983230072969 + 3 ^ 40 * 270003 * 2
def baseEnd_270003 : Nat := 82157817573933241908613

theorem tailTrace_270003 : CollatzResearch.WordTrace tailWord_270003 prefixEnd_270003 82157817573933241908613 := by
  unfold tailWord_270003
  simp only [CollatzResearch.WordTrace]
  refine ⟨9847818440832718686278663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6565212293888479124185775 9847818440832718686278663)
  ·
    refine ⟨14771727661249078029417995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9847818440832718686278663 14771727661249078029417995)
    ·
      refine ⟨22157591491873617044126993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14771727661249078029417995 22157591491873617044126993)
      ·
        refine ⟨16618193618905212783095245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22157591491873617044126993 16618193618905212783095245)
        ·
          refine ⟨6231822607089454793660717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16618193618905212783095245 6231822607089454793660717)
          ·
            refine ⟨2336933477658545547622769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6231822607089454793660717 2336933477658545547622769)
            ·
              refine ⟨1752700108243909160717077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336933477658545547622769 1752700108243909160717077)
              ·
                refine ⟨82157817573933241908613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1752700108243909160717077 82157817573933241908613)
                ·
                  rfl

theorem cell19_270003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_270003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270003 prefixEnd_270003 := by exact prefixLift 270003
  have htrace : WordTrace (prefixWord ++ tailWord_270003) baseStart_270003 baseEnd_270003 := by
    simpa [prefixWord, tailWord_270003, baseEnd_270003] using wordTrace_append hprefix tailTrace_270003
  have hstable : (prefixWord ++ tailWord_270003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270003).length < 2 ^ (prefixWord ++ tailWord_270003).sum := by decide
  have hdescent : baseEnd_270003 < baseStart_270003 := by decide
  rcases family_descends (prefixWord ++ tailWord_270003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270020 : List Nat := [2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_270020 : Nat := 118140960795 + 270020 * 2 ^ 59
def prefixEnd_270020 : Nat := 4983230072969 + 3 ^ 40 * 270020 * 2
def baseEnd_270020 : Nat := 82162990416082239530789

theorem tailTrace_270020 : CollatzResearch.WordTrace tailWord_270020 prefixEnd_270020 82162990416082239530789 := by
  unfold tailWord_270020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924219240885565294823757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6565625654514087059765009 4924219240885565294823757)
  ·
    refine ⟨1846582215332086985558909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4924219240885565294823757 1846582215332086985558909)
    ·
      refine ⟨692468330749532619584591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1846582215332086985558909 692468330749532619584591)
      ·
        refine ⟨1038702496124298929376887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692468330749532619584591 1038702496124298929376887)
        ·
          refine ⟨1558053744186448394065331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038702496124298929376887 1558053744186448394065331)
          ·
            refine ⟨2337080616279672591097997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558053744186448394065331 2337080616279672591097997)
            ·
              refine ⟨876405231104877221661749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2337080616279672591097997 876405231104877221661749)
              ·
                refine ⟨82162990416082239530789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876405231104877221661749 82162990416082239530789)
                ·
                  rfl

theorem cell19_270020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_270020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270020 prefixEnd_270020 := by exact prefixLift 270020
  have htrace : WordTrace (prefixWord ++ tailWord_270020) baseStart_270020 baseEnd_270020 := by
    simpa [prefixWord, tailWord_270020, baseEnd_270020] using wordTrace_append hprefix tailTrace_270020
  have hstable : (prefixWord ++ tailWord_270020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270020).length < 2 ^ (prefixWord ++ tailWord_270020).sum := by decide
  have hdescent : baseEnd_270020 < baseStart_270020 := by decide
  rcases family_descends (prefixWord ++ tailWord_270020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270041 : List Nat := [1, 2, 1, 2, 3, 3, 7]
def baseStart_270041 : Nat := 118140960795 + 270041 * 2 ^ 59
def prefixEnd_270041 : Nat := 4983230072969 + 3 ^ 40 * 270041 * 2
def baseEnd_270041 : Nat := 27389793465853471021355

theorem tailTrace_270041 : CollatzResearch.WordTrace tailWord_270041 prefixEnd_270041 27389793465853471021355 := by
  unfold tailWord_270041
  simp only [CollatzResearch.WordTrace]
  refine ⟨9849204414695051176161977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6566136276463367450774651 9849204414695051176161977)
  ·
    refine ⟨7386903311021288382121483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9849204414695051176161977 7386903311021288382121483)
    ·
      refine ⟨11080354966531932573182225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386903311021288382121483 11080354966531932573182225)
      ·
        refine ⟨8310266224898949429886669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11080354966531932573182225 8310266224898949429886669)
        ·
          refine ⟨3116349834337106036207501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8310266224898949429886669 3116349834337106036207501)
          ·
            refine ⟨1168631187876414763577813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3116349834337106036207501 1168631187876414763577813)
            ·
              refine ⟨27389793465853471021355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1168631187876414763577813 27389793465853471021355)
              ·
                rfl

theorem cell19_270041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_270041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270041 prefixEnd_270041 := by exact prefixLift 270041
  have htrace : WordTrace (prefixWord ++ tailWord_270041) baseStart_270041 baseEnd_270041 := by
    simpa [prefixWord, tailWord_270041, baseEnd_270041] using wordTrace_append hprefix tailTrace_270041
  have hstable : (prefixWord ++ tailWord_270041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270041).length < 2 ^ (prefixWord ++ tailWord_270041).sum := by decide
  have hdescent : baseEnd_270041 < baseStart_270041 := by decide
  rcases family_descends (prefixWord ++ tailWord_270041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270060 : List Nat := [2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_270060 : Nat := 118140960795 + 270060 * 2 ^ 59
def prefixEnd_270060 : Nat := 4983230072969 + 3 ^ 40 * 270060 * 2
def baseEnd_270060 : Nat := 82175161809373998641791

theorem tailTrace_270060 : CollatzResearch.WordTrace tailWord_270060 prefixEnd_270060 82175161809373998641791 := by
  unfold tailWord_270060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924948700813108710551817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6566598267750811614069089 4924948700813108710551817)
  ·
    refine ⟨3693711525609831532913863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4924948700813108710551817 3693711525609831532913863)
    ·
      refine ⟨5540567288414747299370795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3693711525609831532913863 5540567288414747299370795)
      ·
        refine ⟨8310850932622120949056193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5540567288414747299370795 8310850932622120949056193)
        ·
          refine ⟨6233138199466590711792145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8310850932622120949056193 6233138199466590711792145)
          ·
            refine ⟨4674853649599943033844109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6233138199466590711792145 4674853649599943033844109)
            ·
              refine ⟨1753070118599978637691541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4674853649599943033844109 1753070118599978637691541)
              ·
                refine ⟨82175161809373998641791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1753070118599978637691541 82175161809373998641791)
                ·
                  rfl

theorem cell19_270060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_270060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270060 prefixEnd_270060 := by exact prefixLift 270060
  have htrace : WordTrace (prefixWord ++ tailWord_270060) baseStart_270060 baseEnd_270060 := by
    simpa [prefixWord, tailWord_270060, baseEnd_270060] using wordTrace_append hprefix tailTrace_270060
  have hstable : (prefixWord ++ tailWord_270060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270060).length < 2 ^ (prefixWord ++ tailWord_270060).sum := by decide
  have hdescent : baseEnd_270060 < baseStart_270060 := by decide
  rcases family_descends (prefixWord ++ tailWord_270060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270079 : List Nat := [1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_270079 : Nat := 118140960795 + 270079 * 2 ^ 59
def prefixEnd_270079 : Nat := 4983230072969 + 3 ^ 40 * 270079 * 2
def baseEnd_270079 : Nat := 82180943221187584219517

theorem tailTrace_270079 : CollatzResearch.WordTrace tailWord_270079 prefixEnd_270079 82180943221187584219517 := by
  unfold tailWord_270079
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850590388557383666045291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6567060259038255777363527 9850590388557383666045291)
  ·
    refine ⟨14775885582836075499067937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9850590388557383666045291 14775885582836075499067937)
    ·
      refine ⟨11081914187127056624300953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14775885582836075499067937 11081914187127056624300953)
      ·
        refine ⟨8311435640345292468225715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11081914187127056624300953 8311435640345292468225715)
        ·
          refine ⟨12467153460517938702338573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311435640345292468225715 12467153460517938702338573)
          ·
            refine ⟨4675182547694227013376965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12467153460517938702338573 4675182547694227013376965)
            ·
              refine ⟨876596727692667565008181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4675182547694227013376965 876596727692667565008181)
              ·
                refine ⟨82180943221187584219517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876596727692667565008181 82180943221187584219517)
                ·
                  rfl

theorem cell19_270079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_270079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270079 prefixEnd_270079 := by exact prefixLift 270079
  have htrace : WordTrace (prefixWord ++ tailWord_270079) baseStart_270079 baseEnd_270079 := by
    simpa [prefixWord, tailWord_270079, baseEnd_270079] using wordTrace_append hprefix tailTrace_270079
  have hstable : (prefixWord ++ tailWord_270079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270079).length < 2 ^ (prefixWord ++ tailWord_270079).sum := by decide
  have hdescent : baseEnd_270079 < baseStart_270079 := by decide
  rcases family_descends (prefixWord ++ tailWord_270079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270193 : List Nat := [1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_270193 : Nat := 118140960795 + 270193 * 2 ^ 59
def prefixEnd_270193 : Nat := 4983230072969 + 3 ^ 40 * 270193 * 2
def baseEnd_270193 : Nat := 82215631692069097685873

theorem tailTrace_270193 : CollatzResearch.WordTrace tailWord_270193 prefixEnd_270193 82215631692069097685873 := by
  unfold tailWord_270193
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854748310144381135695233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6569832206762920757130155 9854748310144381135695233)
  ·
    refine ⟨7391061232608285851771425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9854748310144381135695233 7391061232608285851771425)
    ·
      refine ⟨5543295924456214388828569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7391061232608285851771425 5543295924456214388828569)
      ·
        refine ⟨4157471943342160791621427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5543295924456214388828569 4157471943342160791621427)
        ·
          refine ⟨6236207915013241187432141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4157471943342160791621427 6236207915013241187432141)
          ·
            refine ⟨2338577968129965445287053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6236207915013241187432141 2338577968129965445287053)
            ·
              refine ⟨876966738048737041982645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2338577968129965445287053 876966738048737041982645)
              ·
                refine ⟨82215631692069097685873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876966738048737041982645 82215631692069097685873)
                ·
                  rfl

theorem cell19_270193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_270193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270193 prefixEnd_270193 := by exact prefixLift 270193
  have htrace : WordTrace (prefixWord ++ tailWord_270193) baseStart_270193 baseEnd_270193 := by
    simpa [prefixWord, tailWord_270193, baseEnd_270193] using wordTrace_append hprefix tailTrace_270193
  have hstable : (prefixWord ++ tailWord_270193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270193).length < 2 ^ (prefixWord ++ tailWord_270193).sum := by decide
  have hdescent : baseEnd_270193 < baseStart_270193 := by decide
  rcases family_descends (prefixWord ++ tailWord_270193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270212 : List Nat := [2, 3, 2, 1, 1, 1, 9]
def baseStart_270212 : Nat := 118140960795 + 270212 * 2 ^ 59
def prefixEnd_270212 : Nat := 4983230072969 + 3 ^ 40 * 270212 * 2
def baseEnd_270212 : Nat := 27407137701294227754533

theorem tailTrace_270212 : CollatzResearch.WordTrace tailWord_270212 prefixEnd_270212 27407137701294227754533 := by
  unfold tailWord_270212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927720648537773690318445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6570294198050364920424593 4927720648537773690318445)
  ·
    refine ⟨1847895243201665133869417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4927720648537773690318445 1847895243201665133869417)
    ·
      refine ⟨1385921432401248850402063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1847895243201665133869417 1385921432401248850402063)
      ·
        refine ⟨2078882148601873275603095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385921432401248850402063 2078882148601873275603095)
        ·
          refine ⟨3118323222902809913404643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078882148601873275603095 3118323222902809913404643)
          ·
            refine ⟨4677484834354214870106965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118323222902809913404643 4677484834354214870106965)
            ·
              refine ⟨27407137701294227754533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4677484834354214870106965 27407137701294227754533)
              ·
                rfl

theorem cell19_270212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_270212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270212 prefixEnd_270212 := by exact prefixLift 270212
  have htrace : WordTrace (prefixWord ++ tailWord_270212) baseStart_270212 baseEnd_270212 := by
    simpa [prefixWord, tailWord_270212, baseEnd_270212] using wordTrace_append hprefix tailTrace_270212
  have hstable : (prefixWord ++ tailWord_270212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270212).length < 2 ^ (prefixWord ++ tailWord_270212).sum := by decide
  have hdescent : baseEnd_270212 < baseStart_270212 := by decide
  rcases family_descends (prefixWord ++ tailWord_270212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270231 : List Nat := [1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_270231 : Nat := 118140960795 + 270231 * 2 ^ 59
def prefixEnd_270231 : Nat := 4983230072969 + 3 ^ 40 * 270231 * 2
def baseEnd_270231 : Nat := 82227194515696268841325

theorem tailTrace_270231 : CollatzResearch.WordTrace tailWord_270231 prefixEnd_270231 82227194515696268841325 := by
  unfold tailWord_270231
  simp only [CollatzResearch.WordTrace]
  refine ⟨9856134284006713625578547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6570756189337809083719031 9856134284006713625578547)
  ·
    refine ⟨14784201426010070438367821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9856134284006713625578547 14784201426010070438367821)
    ·
      refine ⟨5544075534753776414387933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14784201426010070438367821 5544075534753776414387933)
      ·
        refine ⟨2079028325532666155395475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5544075534753776414387933 2079028325532666155395475)
        ·
          refine ⟨3118542488298999233093213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079028325532666155395475 3118542488298999233093213)
          ·
            refine ⟨1169453433112124712409955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3118542488298999233093213 1169453433112124712409955)
            ·
              refine ⟨1754180149668187068614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169453433112124712409955 1754180149668187068614933)
              ·
                refine ⟨82227194515696268841325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1754180149668187068614933 82227194515696268841325)
                ·
                  rfl

theorem cell19_270231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_270231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270231 prefixEnd_270231 := by exact prefixLift 270231
  have htrace : WordTrace (prefixWord ++ tailWord_270231) baseStart_270231 baseEnd_270231 := by
    simpa [prefixWord, tailWord_270231, baseEnd_270231] using wordTrace_append hprefix tailTrace_270231
  have hstable : (prefixWord ++ tailWord_270231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270231).length < 2 ^ (prefixWord ++ tailWord_270231).sum := by decide
  have hdescent : baseEnd_270231 < baseStart_270231 := by decide
  rcases family_descends (prefixWord ++ tailWord_270231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270269 : List Nat := [1, 4, 1, 2, 3, 8]
def baseStart_270269 : Nat := 118140960795 + 270269 * 2 ^ 59
def prefixEnd_270269 : Nat := 4983230072969 + 3 ^ 40 * 270269 * 2
def baseEnd_270269 : Nat := 9137639704369271110753

theorem tailTrace_270269 : CollatzResearch.WordTrace tailWord_270269 prefixEnd_270269 9137639704369271110753 := by
  unfold tailWord_270269
  simp only [CollatzResearch.WordTrace]
  refine ⟨9857520257869046115461861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6571680171912697410307907 9857520257869046115461861)
  ·
    refine ⟨1848285048350446146649099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9857520257869046115461861 1848285048350446146649099)
    ·
      refine ⟨2772427572525669219973649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848285048350446146649099 2772427572525669219973649)
      ·
        refine ⟨2079320679394251914980237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2772427572525669219973649 2079320679394251914980237)
        ·
          refine ⟨779745254772844468117589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2079320679394251914980237 779745254772844468117589)
          ·
            refine ⟨9137639704369271110753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 779745254772844468117589 9137639704369271110753)
            ·
              rfl

theorem cell19_270269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_270269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270269 prefixEnd_270269 := by exact prefixLift 270269
  have htrace : WordTrace (prefixWord ++ tailWord_270269) baseStart_270269 baseEnd_270269 := by
    simpa [prefixWord, tailWord_270269, baseEnd_270269] using wordTrace_append hprefix tailTrace_270269
  have hstable : (prefixWord ++ tailWord_270269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270269).length < 2 ^ (prefixWord ++ tailWord_270269).sum := by decide
  have hdescent : baseEnd_270269 < baseStart_270269 := by decide
  rcases family_descends (prefixWord ++ tailWord_270269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270288 : List Nat := [2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_270288 : Nat := 118140960795 + 270288 * 2 ^ 59
def prefixEnd_270288 : Nat := 4983230072969 + 3 ^ 40 * 270288 * 2
def baseEnd_270288 : Nat := 82244538751137025574503

theorem tailTrace_270288 : CollatzResearch.WordTrace tailWord_270288 prefixEnd_270288 82244538751137025574503 := by
  unfold tailWord_270288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929106622400106180201759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6572142163200141573602345 4929106622400106180201759)
  ·
    refine ⟨7393659933600159270302639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4929106622400106180201759 7393659933600159270302639)
    ·
      refine ⟨11090489900400238905453959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7393659933600159270302639 11090489900400238905453959)
      ·
        refine ⟨16635734850600358358180939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11090489900400238905453959 16635734850600358358180939)
        ·
          refine ⟨24953602275900537537271409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16635734850600358358180939 24953602275900537537271409)
          ·
            refine ⟨18715201706925403152953557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24953602275900537537271409 18715201706925403152953557)
            ·
              refine ⟨438637540006064136397349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18715201706925403152953557 438637540006064136397349)
              ·
                refine ⟨82244538751137025574503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438637540006064136397349 82244538751137025574503)
                ·
                  rfl

theorem cell19_270288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_270288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270288 prefixEnd_270288 := by exact prefixLift 270288
  have htrace : WordTrace (prefixWord ++ tailWord_270288) baseStart_270288 baseEnd_270288 := by
    simpa [prefixWord, tailWord_270288, baseEnd_270288] using wordTrace_append hprefix tailTrace_270288
  have hstable : (prefixWord ++ tailWord_270288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270288).length < 2 ^ (prefixWord ++ tailWord_270288).sum := by decide
  have hdescent : baseEnd_270288 < baseStart_270288 := by decide
  rcases family_descends (prefixWord ++ tailWord_270288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270356 : List Nat := [2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_270356 : Nat := 118140960795 + 270356 * 2 ^ 59
def prefixEnd_270356 : Nat := 4983230072969 + 3 ^ 40 * 270356 * 2
def baseEnd_270356 : Nat := 82265230119733016063207

theorem tailTrace_270356 : CollatzResearch.WordTrace tailWord_270356 prefixEnd_270356 82265230119733016063207 := by
  unfold tailWord_270356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930346704276929986939461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6573795605702573315919281 4930346704276929986939461)
  ·
    refine ⟨924440007051924372551149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4930346704276929986939461 924440007051924372551149)
    ·
      refine ⟨346665002644471639706681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 924440007051924372551149 346665002644471639706681)
      ·
        refine ⟨259998751983353729780011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346665002644471639706681 259998751983353729780011)
        ·
          refine ⟨389998127975030594670017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259998751983353729780011 389998127975030594670017)
          ·
            refine ⟨292498595981272946002513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389998127975030594670017 292498595981272946002513)
            ·
              refine ⟨219373946985954709501885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292498595981272946002513 219373946985954709501885)
              ·
                refine ⟨82265230119733016063207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219373946985954709501885 82265230119733016063207)
                ·
                  rfl

theorem cell19_270356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_270356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270356 prefixEnd_270356 := by exact prefixLift 270356
  have htrace : WordTrace (prefixWord ++ tailWord_270356) baseStart_270356 baseEnd_270356 := by
    simpa [prefixWord, tailWord_270356, baseEnd_270356] using wordTrace_append hprefix tailTrace_270356
  have hstable : (prefixWord ++ tailWord_270356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270356).length < 2 ^ (prefixWord ++ tailWord_270356).sum := by decide
  have hdescent : baseEnd_270356 < baseStart_270356 := by decide
  rcases family_descends (prefixWord ++ tailWord_270356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270362 : List Nat := [3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_270362 : Nat := 118140960795 + 270362 * 2 ^ 59
def prefixEnd_270362 : Nat := 4983230072969 + 3 ^ 40 * 270362 * 2
def baseEnd_270362 : Nat := 82267055828726779929857

theorem tailTrace_270362 : CollatzResearch.WordTrace tailWord_270362 prefixEnd_270362 82267055828726779929857 := by
  unfold tailWord_270362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465228061633030749649335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6573941497688081999064893 2465228061633030749649335)
  ·
    refine ⟨3697842092449546124474003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465228061633030749649335 3697842092449546124474003)
    ·
      refine ⟨5546763138674319186711005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3697842092449546124474003 5546763138674319186711005)
      ·
        refine ⟨2080036177002869695016627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5546763138674319186711005 2080036177002869695016627)
        ·
          refine ⟨3120054265504304542524941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080036177002869695016627 3120054265504304542524941)
          ·
            refine ⟨1170020349564114203446853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3120054265504304542524941 1170020349564114203446853)
            ·
              refine ⟨219378815543271413146285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1170020349564114203446853 219378815543271413146285)
              ·
                refine ⟨82267055828726779929857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219378815543271413146285 82267055828726779929857)
                ·
                  rfl

theorem cell19_270362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_270362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270362 prefixEnd_270362 := by exact prefixLift 270362
  have htrace : WordTrace (prefixWord ++ tailWord_270362) baseStart_270362 baseEnd_270362 := by
    simpa [prefixWord, tailWord_270362, baseEnd_270362] using wordTrace_append hprefix tailTrace_270362
  have hstable : (prefixWord ++ tailWord_270362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270362).length < 2 ^ (prefixWord ++ tailWord_270362).sum := by decide
  have hdescent : baseEnd_270362 < baseStart_270362 := by decide
  rcases family_descends (prefixWord ++ tailWord_270362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270398 : List Nat := [4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_270398 : Nat := 118140960795 + 270398 * 2 ^ 59
def prefixEnd_270398 : Nat := 4983230072969 + 3 ^ 40 * 270398 * 2
def baseEnd_270398 : Nat := 82278010082689363129759

theorem tailTrace_270398 : CollatzResearch.WordTrace tailWord_270398 prefixEnd_270398 82278010082689363129759 := by
  unfold tailWord_270398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232778159300212643363481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6574816849601134097938565 1232778159300212643363481)
  ·
    refine ⟨924583619475159482522611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1232778159300212643363481 924583619475159482522611)
    ·
      refine ⟨1386875429212739223783917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924583619475159482522611 1386875429212739223783917)
      ·
        refine ⟨520078285954777208918969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1386875429212739223783917 520078285954777208918969)
        ·
          refine ⟨390058714466082906689227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520078285954777208918969 390058714466082906689227)
          ·
            refine ⟨585088071699124360033841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390058714466082906689227 585088071699124360033841)
            ·
              refine ⟨438816053774343270025381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585088071699124360033841 438816053774343270025381)
              ·
                refine ⟨82278010082689363129759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438816053774343270025381 82278010082689363129759)
                ·
                  rfl

theorem cell19_270398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_270398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270398 prefixEnd_270398 := by exact prefixLift 270398
  have htrace : WordTrace (prefixWord ++ tailWord_270398) baseStart_270398 baseEnd_270398 := by
    simpa [prefixWord, tailWord_270398, baseEnd_270398] using wordTrace_append hprefix tailTrace_270398
  have hstable : (prefixWord ++ tailWord_270398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270398).length < 2 ^ (prefixWord ++ tailWord_270398).sum := by decide
  have hdescent : baseEnd_270398 < baseStart_270398 := by decide
  rcases family_descends (prefixWord ++ tailWord_270398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270421 : List Nat := [1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_270421 : Nat := 118140960795 + 270421 * 2 ^ 59
def prefixEnd_270421 : Nat := 4983230072969 + 3 ^ 40 * 270421 * 2
def baseEnd_270421 : Nat := 82285008633832124618585

theorem tailTrace_270421 : CollatzResearch.WordTrace tailWord_270421 prefixEnd_270421 82285008633832124618585 := by
  unfold tailWord_270421
  simp only [CollatzResearch.WordTrace]
  refine ⟨9863064153318376074995117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6575376102212250716663411 9863064153318376074995117)
  ·
    refine ⟨3698649057494391028123169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9863064153318376074995117 3698649057494391028123169)
    ·
      refine ⟨2773986793120793271092377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3698649057494391028123169 2773986793120793271092377)
      ·
        refine ⟨2080490094840594953319283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773986793120793271092377 2080490094840594953319283)
        ·
          refine ⟨3120735142260892429978925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080490094840594953319283 3120735142260892429978925)
          ·
            refine ⟨1170275678347834661242097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3120735142260892429978925 1170275678347834661242097)
            ·
              refine ⟨877706758760875995931573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170275678347834661242097 877706758760875995931573)
              ·
                refine ⟨82285008633832124618585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877706758760875995931573 82285008633832124618585)
                ·
                  rfl

theorem cell19_270421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_270421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270421 prefixEnd_270421 := by exact prefixLift 270421
  have htrace : WordTrace (prefixWord ++ tailWord_270421) baseStart_270421 baseEnd_270421 := by
    simpa [prefixWord, tailWord_270421, baseEnd_270421] using wordTrace_append hprefix tailTrace_270421
  have hstable : (prefixWord ++ tailWord_270421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270421).length < 2 ^ (prefixWord ++ tailWord_270421).sum := by decide
  have hdescent : baseEnd_270421 < baseStart_270421 := by decide
  rcases family_descends (prefixWord ++ tailWord_270421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270457 : List Nat := [1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_270457 : Nat := 118140960795 + 270457 * 2 ^ 59
def prefixEnd_270457 : Nat := 4983230072969 + 3 ^ 40 * 270457 * 2
def baseEnd_270457 : Nat := 82295962887794707818487

theorem tailTrace_270457 : CollatzResearch.WordTrace tailWord_270457 prefixEnd_270457 82295962887794707818487 := by
  unfold tailWord_270457
  simp only [CollatzResearch.WordTrace]
  refine ⟨9864377181187954223305625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6576251454125302815537083 9864377181187954223305625)
  ·
    refine ⟨7398282885890965667479219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9864377181187954223305625 7398282885890965667479219)
    ·
      refine ⟨11097424328836448501218829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7398282885890965667479219 11097424328836448501218829)
      ·
        refine ⟨4161534123313668187957061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11097424328836448501218829 4161534123313668187957061)
        ·
          refine ⟨780287648121312785241949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4161534123313668187957061 780287648121312785241949)
          ·
            refine ⟨292607868045492294465731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 780287648121312785241949 292607868045492294465731)
            ·
              refine ⟨438911802068238441698597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292607868045492294465731 438911802068238441698597)
              ·
                refine ⟨82295962887794707818487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438911802068238441698597 82295962887794707818487)
                ·
                  rfl

theorem cell19_270457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_270457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270457 prefixEnd_270457 := by exact prefixLift 270457
  have htrace : WordTrace (prefixWord ++ tailWord_270457) baseStart_270457 baseEnd_270457 := by
    simpa [prefixWord, tailWord_270457, baseEnd_270457] using wordTrace_append hprefix tailTrace_270457
  have hstable : (prefixWord ++ tailWord_270457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270457).length < 2 ^ (prefixWord ++ tailWord_270457).sum := by decide
  have hdescent : baseEnd_270457 < baseStart_270457 := by decide
  rcases family_descends (prefixWord ++ tailWord_270457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270497 : List Nat := [1, 2, 3, 3, 1, 3, 6]
def baseStart_270497 : Nat := 118140960795 + 270497 * 2 ^ 59
def prefixEnd_270497 : Nat := 4983230072969 + 3 ^ 40 * 270497 * 2
def baseEnd_270497 : Nat := 27436044760362155643163

theorem tailTrace_270497 : CollatzResearch.WordTrace tailWord_270497 prefixEnd_270497 27436044760362155643163 := by
  unfold tailWord_270497
  simp only [CollatzResearch.WordTrace]
  refine ⟨9865836101043041054761745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6577224067362027369841163 9865836101043041054761745)
  ·
    refine ⟨7399377075782280791071309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9865836101043041054761745 7399377075782280791071309)
    ·
      refine ⟨2774766403418355296651741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7399377075782280791071309 2774766403418355296651741)
      ·
        refine ⟨1040537401281883236244403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2774766403418355296651741 1040537401281883236244403)
        ·
          refine ⟨1560806101922824854366605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040537401281883236244403 1560806101922824854366605)
          ·
            refine ⟨585302288221059320387477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1560806101922824854366605 585302288221059320387477)
            ·
              refine ⟨27436044760362155643163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 585302288221059320387477 27436044760362155643163)
              ·
                rfl

theorem cell19_270497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_270497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270497 prefixEnd_270497 := by exact prefixLift 270497
  have htrace : WordTrace (prefixWord ++ tailWord_270497) baseStart_270497 baseEnd_270497 := by
    simpa [prefixWord, tailWord_270497, baseEnd_270497] using wordTrace_append hprefix tailTrace_270497
  have hstable : (prefixWord ++ tailWord_270497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270497).length < 2 ^ (prefixWord ++ tailWord_270497).sum := by decide
  have hdescent : baseEnd_270497 < baseStart_270497 := by decide
  rcases family_descends (prefixWord ++ tailWord_270497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270529 : List Nat := [1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_270529 : Nat := 118140960795 + 270529 * 2 ^ 59
def prefixEnd_270529 : Nat := 4983230072969 + 3 ^ 40 * 270529 * 2
def baseEnd_270529 : Nat := 82317871395719874218291

theorem tailTrace_270529 : CollatzResearch.WordTrace tailWord_270529 prefixEnd_270529 82317871395719874218291 := by
  unfold tailWord_270529
  simp only [CollatzResearch.WordTrace]
  refine ⟨9867003236927110519926641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6578002157951407013284427 9867003236927110519926641)
  ·
    refine ⟨7400252427695332889944981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9867003236927110519926641 7400252427695332889944981)
    ·
      refine ⟨346886832548218729216171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7400252427695332889944981 346886832548218729216171)
      ·
        refine ⟨520330248822328093824257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346886832548218729216171 520330248822328093824257)
        ·
          refine ⟨390247686616746070368193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520330248822328093824257 390247686616746070368193)
          ·
            refine ⟨292685764962559552776145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390247686616746070368193 292685764962559552776145)
            ·
              refine ⟨219514323721919664582109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292685764962559552776145 219514323721919664582109)
              ·
                refine ⟨82317871395719874218291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219514323721919664582109 82317871395719874218291)
                ·
                  rfl

theorem cell19_270529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_270529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270529 prefixEnd_270529 := by exact prefixLift 270529
  have htrace : WordTrace (prefixWord ++ tailWord_270529) baseStart_270529 baseEnd_270529 := by
    simpa [prefixWord, tailWord_270529, baseEnd_270529] using wordTrace_append hprefix tailTrace_270529
  have hstable : (prefixWord ++ tailWord_270529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270529).length < 2 ^ (prefixWord ++ tailWord_270529).sum := by decide
  have hdescent : baseEnd_270529 < baseStart_270529 := by decide
  rcases family_descends (prefixWord ++ tailWord_270529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270550 : List Nat := [5, 2, 1, 2, 1, 3, 5]
def baseStart_270550 : Nat := 118140960795 + 270550 * 2 ^ 59
def prefixEnd_270550 : Nat := 4983230072969 + 3 ^ 40 * 270550 * 2
def baseEnd_270550 : Nat := 27441420459066015917189

theorem tailTrace_270550 : CollatzResearch.WordTrace tailWord_270550 prefixEnd_270550 27441420459066015917189 := by
  unfold tailWord_270550
  simp only [CollatzResearch.WordTrace]
  refine ⟨616735573115689444152569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6578512779900687404294069 616735573115689444152569)
  ·
    refine ⟨462551679836767083114427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 616735573115689444152569 462551679836767083114427)
    ·
      refine ⟨693827519755150624671641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462551679836767083114427 693827519755150624671641)
      ·
        refine ⟨520370639816362968503731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693827519755150624671641 520370639816362968503731)
        ·
          refine ⟨780555959724544452755597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520370639816362968503731 780555959724544452755597)
          ·
            refine ⟨292708484896704169783349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 780555959724544452755597 292708484896704169783349)
            ·
              refine ⟨27441420459066015917189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 292708484896704169783349 27441420459066015917189)
              ·
                rfl

theorem cell19_270550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_270550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270550 prefixEnd_270550 := by exact prefixLift 270550
  have htrace : WordTrace (prefixWord ++ tailWord_270550) baseStart_270550 baseEnd_270550 := by
    simpa [prefixWord, tailWord_270550, baseEnd_270550] using wordTrace_append hprefix tailTrace_270550
  have hstable : (prefixWord ++ tailWord_270550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270550).length < 2 ^ (prefixWord ++ tailWord_270550).sum := by decide
  have hdescent : baseEnd_270550 < baseStart_270550 := by decide
  rcases family_descends (prefixWord ++ tailWord_270550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270628 : List Nat := [2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_270628 : Nat := 118140960795 + 270628 * 2 ^ 59
def prefixEnd_270628 : Nat := 4983230072969 + 3 ^ 40 * 270628 * 2
def baseEnd_270628 : Nat := 82347995594116978018021

theorem tailTrace_270628 : CollatzResearch.WordTrace tailWord_270628 prefixEnd_270628 82347995594116978018021 := by
  unfold tailWord_270628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935307031784225213890269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6580409375712300285187025 4935307031784225213890269)
  ·
    refine ⟨1850740136919084455208851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4935307031784225213890269 1850740136919084455208851)
    ·
      refine ⟨2776110205378626682813277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850740136919084455208851 2776110205378626682813277)
      ·
        refine ⟨1041041327016985006054979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2776110205378626682813277 1041041327016985006054979)
        ·
          refine ⟨1561561990525477509082469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041041327016985006054979 1561561990525477509082469)
          ·
            refine ⟨292792873223527032952963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1561561990525477509082469 292792873223527032952963)
            ·
              refine ⟨439189309835290549429445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292792873223527032952963 439189309835290549429445)
              ·
                refine ⟨82347995594116978018021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439189309835290549429445 82347995594116978018021)
                ·
                  rfl

theorem cell19_270628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_270628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270628 prefixEnd_270628 := by exact prefixLift 270628
  have htrace : WordTrace (prefixWord ++ tailWord_270628) baseStart_270628 baseEnd_270628 := by
    simpa [prefixWord, tailWord_270628, baseEnd_270628] using wordTrace_append hprefix tailTrace_270628
  have hstable : (prefixWord ++ tailWord_270628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270628).length < 2 ^ (prefixWord ++ tailWord_270628).sum := by decide
  have hdescent : baseEnd_270628 < baseStart_270628 := by decide
  rcases family_descends (prefixWord ++ tailWord_270628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270704 : List Nat := [2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_270704 : Nat := 118140960795 + 270704 * 2 ^ 59
def prefixEnd_270704 : Nat := 4983230072969 + 3 ^ 40 * 270704 * 2
def baseEnd_270704 : Nat := 82371121241371320328925

theorem tailTrace_270704 : CollatzResearch.WordTrace tailWord_270704 prefixEnd_270704 82371121241371320328925 := by
  unfold tailWord_270704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936693005646557703773583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6582257340862076938364777 4936693005646557703773583)
  ·
    refine ⟨7405039508469836555660375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4936693005646557703773583 7405039508469836555660375)
    ·
      refine ⟨11107559262704754833490563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7405039508469836555660375 11107559262704754833490563)
      ·
        refine ⟨16661338894057132250235845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11107559262704754833490563 16661338894057132250235845)
        ·
          refine ⟨3124001042635712296919221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16661338894057132250235845 3124001042635712296919221)
          ·
            refine ⟨292875097747098027836177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3124001042635712296919221 292875097747098027836177)
            ·
              refine ⟨219656323310323520877133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292875097747098027836177 219656323310323520877133)
              ·
                refine ⟨82371121241371320328925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219656323310323520877133 82371121241371320328925)
                ·
                  rfl

theorem cell19_270704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_270704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270704 prefixEnd_270704 := by exact prefixLift 270704
  have htrace : WordTrace (prefixWord ++ tailWord_270704) baseStart_270704 baseEnd_270704 := by
    simpa [prefixWord, tailWord_270704, baseEnd_270704] using wordTrace_append hprefix tailTrace_270704
  have hstable : (prefixWord ++ tailWord_270704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270704).length < 2 ^ (prefixWord ++ tailWord_270704).sum := by decide
  have hdescent : baseEnd_270704 < baseStart_270704 := by decide
  rcases family_descends (prefixWord ++ tailWord_270704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270706 : List Nat := [3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_270706 : Nat := 118140960795 + 270706 * 2 ^ 59
def prefixEnd_270706 : Nat := 4983230072969 + 3 ^ 40 * 270706 * 2
def baseEnd_270706 : Nat := 82371729811035908284475

theorem tailTrace_270706 : CollatzResearch.WordTrace tailWord_270706 prefixEnd_270706 82371729811035908284475 := by
  unfold tailWord_270706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468364739321467437279993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6582305971523913166079981 2468364739321467437279993)
  ·
    refine ⟨1851273554491100577959995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2468364739321467437279993 1851273554491100577959995)
    ·
      refine ⟨2776910331736650866939993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851273554491100577959995 2776910331736650866939993)
      ·
        refine ⟨2082682748802488150204995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2776910331736650866939993 2082682748802488150204995)
        ·
          refine ⟨3124024123203732225307493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082682748802488150204995 3124024123203732225307493)
          ·
            refine ⟨585754523100699792245155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3124024123203732225307493 585754523100699792245155)
            ·
              refine ⟨878631784651049688367733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585754523100699792245155 878631784651049688367733)
              ·
                refine ⟨82371729811035908284475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 878631784651049688367733 82371729811035908284475)
                ·
                  rfl

theorem cell19_270706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_270706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270706 prefixEnd_270706 := by exact prefixLift 270706
  have htrace : WordTrace (prefixWord ++ tailWord_270706) baseStart_270706 baseEnd_270706 := by
    simpa [prefixWord, tailWord_270706, baseEnd_270706] using wordTrace_append hprefix tailTrace_270706
  have hstable : (prefixWord ++ tailWord_270706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270706).length < 2 ^ (prefixWord ++ tailWord_270706).sum := by decide
  have hdescent : baseEnd_270706 < baseStart_270706 := by decide
  rcases family_descends (prefixWord ++ tailWord_270706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270723 : List Nat := [1, 1, 1, 3, 7, 1, 5]
def baseStart_270723 : Nat := 118140960795 + 270723 * 2 ^ 59
def prefixEnd_270723 : Nat := 4983230072969 + 3 ^ 40 * 270723 * 2
def baseEnd_270723 : Nat := 27458967551061635302217

theorem tailTrace_270723 : CollatzResearch.WordTrace tailWord_270723 prefixEnd_270723 27458967551061635302217 := by
  unfold tailWord_270723
  simp only [CollatzResearch.WordTrace]
  refine ⟨9874078998224281652488823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6582719332149521101659215 9874078998224281652488823)
  ·
    refine ⟨14811118497336422478733235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9874078998224281652488823 14811118497336422478733235)
    ·
      refine ⟨22216677746004633718099853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14811118497336422478733235 22216677746004633718099853)
      ·
        refine ⟨8331254154751737644287445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22216677746004633718099853 8331254154751737644287445)
        ·
          refine ⟨195263769251993851037987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8331254154751737644287445 195263769251993851037987)
          ·
            refine ⟨292895653877990776556981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195263769251993851037987 292895653877990776556981)
            ·
              refine ⟨27458967551061635302217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 292895653877990776556981 27458967551061635302217)
              ·
                rfl

theorem cell19_270723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_270723 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270723 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270723 prefixEnd_270723 := by exact prefixLift 270723
  have htrace : WordTrace (prefixWord ++ tailWord_270723) baseStart_270723 baseEnd_270723 := by
    simpa [prefixWord, tailWord_270723, baseEnd_270723] using wordTrace_append hprefix tailTrace_270723
  have hstable : (prefixWord ++ tailWord_270723).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270723).length < 2 ^ (prefixWord ++ tailWord_270723).sum := by decide
  have hdescent : baseEnd_270723 < baseStart_270723 := by decide
  rcases family_descends (prefixWord ++ tailWord_270723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270744 : List Nat := [2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_270744 : Nat := 118140960795 + 270744 * 2 ^ 59
def prefixEnd_270744 : Nat := 4983230072969 + 3 ^ 40 * 270744 * 2
def baseEnd_270744 : Nat := 82383292634663079439927

theorem tailTrace_270744 : CollatzResearch.WordTrace tailWord_270744 prefixEnd_270744 82383292634663079439927 := by
  unfold tailWord_270744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937422465574101119501643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6583229954098801492668857 4937422465574101119501643)
  ·
    refine ⟨7406133698361151679252465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4937422465574101119501643 7406133698361151679252465)
    ·
      refine ⟨5554600273770863759439349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7406133698361151679252465 5554600273770863759439349)
      ·
        refine ⟨520743775666018477447439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5554600273770863759439349 520743775666018477447439)
        ·
          refine ⟨781115663499027716171159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520743775666018477447439 781115663499027716171159)
          ·
            refine ⟨1171673495248541574256739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781115663499027716171159 1171673495248541574256739)
            ·
              refine ⟨1757510242872812361385109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171673495248541574256739 1757510242872812361385109)
              ·
                refine ⟨82383292634663079439927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1757510242872812361385109 82383292634663079439927)
                ·
                  rfl

theorem cell19_270744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_270744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270744 prefixEnd_270744 := by exact prefixLift 270744
  have htrace : WordTrace (prefixWord ++ tailWord_270744) baseStart_270744 baseEnd_270744 := by
    simpa [prefixWord, tailWord_270744, baseEnd_270744] using wordTrace_append hprefix tailTrace_270744
  have hstable : (prefixWord ++ tailWord_270744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270744).length < 2 ^ (prefixWord ++ tailWord_270744).sum := by decide
  have hdescent : baseEnd_270744 < baseStart_270744 := by decide
  rcases family_descends (prefixWord ++ tailWord_270744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270837 : List Nat := [1, 3, 5, 1, 2, 1, 6]
def baseStart_270837 : Nat := 118140960795 + 270837 * 2 ^ 59
def prefixEnd_270837 : Nat := 4983230072969 + 3 ^ 40 * 270837 * 2
def baseEnd_270837 : Nat := 27470530374688806457669

theorem tailTrace_270837 : CollatzResearch.WordTrace tailWord_270837 prefixEnd_270837 27470530374688806457669 := by
  unfold tailWord_270837
  simp only [CollatzResearch.WordTrace]
  refine ⟨9878236919811279122138765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6585491279874186081425843 9878236919811279122138765)
  ·
    refine ⟨3704338844929229670802037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9878236919811279122138765 3704338844929229670802037)
    ·
      refine ⟨347281766712115281637691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3704338844929229670802037 347281766712115281637691)
      ·
        refine ⟨520922650068172922456537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347281766712115281637691 520922650068172922456537)
        ·
          refine ⟨390691987551129691842403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520922650068172922456537 390691987551129691842403)
          ·
            refine ⟨586037981326694537763605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390691987551129691842403 586037981326694537763605)
            ·
              refine ⟨27470530374688806457669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 586037981326694537763605 27470530374688806457669)
              ·
                rfl

theorem cell19_270837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_270837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270837 prefixEnd_270837 := by exact prefixLift 270837
  have htrace : WordTrace (prefixWord ++ tailWord_270837) baseStart_270837 baseEnd_270837 := by
    simpa [prefixWord, tailWord_270837, baseEnd_270837] using wordTrace_append hprefix tailTrace_270837
  have hstable : (prefixWord ++ tailWord_270837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270837).length < 2 ^ (prefixWord ++ tailWord_270837).sum := by decide
  have hdescent : baseEnd_270837 < baseStart_270837 := by decide
  rcases family_descends (prefixWord ++ tailWord_270837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270871 : List Nat := [1, 1, 3, 6, 2, 1, 2, 3]
def baseStart_270871 : Nat := 118140960795 + 270871 * 2 ^ 59
def prefixEnd_270871 : Nat := 4983230072969 + 3 ^ 40 * 270871 * 2
def baseEnd_270871 : Nat := 82421936808364414617359

theorem tailTrace_270871 : CollatzResearch.WordTrace tailWord_270871 prefixEnd_270871 82421936808364414617359 := by
  unfold tailWord_270871
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879477001688102928876467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6586318001125401952584311 9879477001688102928876467)
  ·
    refine ⟨14819215502532154393314701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9879477001688102928876467 14819215502532154393314701)
    ·
      refine ⟨5557205813449557897493013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14819215502532154393314701 5557205813449557897493013)
      ·
        refine ⟨260494022505448026444985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5557205813449557897493013 260494022505448026444985)
        ·
          refine ⟨195370516879086019833739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260494022505448026444985 195370516879086019833739)
          ·
            refine ⟨293055775318629029750609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195370516879086019833739 293055775318629029750609)
            ·
              refine ⟨219791831488971772312957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293055775318629029750609 219791831488971772312957)
              ·
                refine ⟨82421936808364414617359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219791831488971772312957 82421936808364414617359)
                ·
                  rfl

theorem cell19_270871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_270871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270871 prefixEnd_270871 := by exact prefixLift 270871
  have htrace : WordTrace (prefixWord ++ tailWord_270871) baseStart_270871 baseEnd_270871 := by
    simpa [prefixWord, tailWord_270871, baseEnd_270871] using wordTrace_append hprefix tailTrace_270871
  have hstable : (prefixWord ++ tailWord_270871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270871).length < 2 ^ (prefixWord ++ tailWord_270871).sum := by decide
  have hdescent : baseEnd_270871 < baseStart_270871 := by decide
  rcases family_descends (prefixWord ++ tailWord_270871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270877 : List Nat := [1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_270877 : Nat := 118140960795 + 270877 * 2 ^ 59
def prefixEnd_270877 : Nat := 4983230072969 + 3 ^ 40 * 270877 * 2
def baseEnd_270877 : Nat := 82423762517358178484009

theorem tailTrace_270877 : CollatzResearch.WordTrace tailWord_270877 prefixEnd_270877 82423762517358178484009 := by
  unfold tailWord_270877
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879695839666365953594885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6586463893110910635729923 9879695839666365953594885)
  ·
    refine ⟨1852442969937443616299041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9879695839666365953594885 1852442969937443616299041)
    ·
      refine ⟨1389332227453082712224281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1852442969937443616299041 1389332227453082712224281)
      ·
        refine ⟨1041999170589812034168211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1389332227453082712224281 1041999170589812034168211)
        ·
          refine ⟨1562998755884718051252317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041999170589812034168211 1562998755884718051252317)
          ·
            refine ⟨586124533456769269219619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1562998755884718051252317 586124533456769269219619)
            ·
              refine ⟨879186800185153903829429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586124533456769269219619 879186800185153903829429)
              ·
                refine ⟨82423762517358178484009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879186800185153903829429 82423762517358178484009)
                ·
                  rfl

theorem cell19_270877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_270877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270877 prefixEnd_270877 := by exact prefixLift 270877
  have htrace : WordTrace (prefixWord ++ tailWord_270877) baseStart_270877 baseEnd_270877 := by
    simpa [prefixWord, tailWord_270877, baseEnd_270877] using wordTrace_append hprefix tailTrace_270877
  have hstable : (prefixWord ++ tailWord_270877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270877).length < 2 ^ (prefixWord ++ tailWord_270877).sum := by decide
  have hdescent : baseEnd_270877 < baseStart_270877 := by decide
  rcases family_descends (prefixWord ++ tailWord_270877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270894 : List Nat := [4, 1, 3, 1, 3, 2, 5]
def baseStart_270894 : Nat := 118140960795 + 270894 * 2 ^ 59
def prefixEnd_270894 : Nat := 4983230072969 + 3 ^ 40 * 270894 * 2
def baseEnd_270894 : Nat := 27476311786502392035395

theorem tailTrace_270894 : CollatzResearch.WordTrace tailWord_270894 prefixEnd_270894 27476311786502392035395 := by
  unfold tailWord_270894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235039485075597232120467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6586877253736518571309157 1235039485075597232120467)
  ·
    refine ⟨1852559227613395848180701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235039485075597232120467 1852559227613395848180701)
    ·
      refine ⟨694709710355023443067763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1852559227613395848180701 694709710355023443067763)
      ·
        refine ⟨1042064565532535164601645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694709710355023443067763 1042064565532535164601645)
        ·
          refine ⟨390774212074700686725617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1042064565532535164601645 390774212074700686725617)
          ·
            refine ⟨293080659056025515044213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390774212074700686725617 293080659056025515044213)
            ·
              refine ⟨27476311786502392035395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 293080659056025515044213 27476311786502392035395)
              ·
                rfl

theorem cell19_270894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_270894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270894 prefixEnd_270894 := by exact prefixLift 270894
  have htrace : WordTrace (prefixWord ++ tailWord_270894) baseStart_270894 baseEnd_270894 := by
    simpa [prefixWord, tailWord_270894, baseEnd_270894] using wordTrace_append hprefix tailTrace_270894
  have hstable : (prefixWord ++ tailWord_270894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270894).length < 2 ^ (prefixWord ++ tailWord_270894).sum := by decide
  have hdescent : baseEnd_270894 < baseStart_270894 := by decide
  rcases family_descends (prefixWord ++ tailWord_270894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270898 : List Nat := [3, 2, 1, 1, 2, 1, 9]
def baseStart_270898 : Nat := 118140960795 + 270898 * 2 ^ 59
def prefixEnd_270898 : Nat := 4983230072969 + 3 ^ 40 * 270898 * 2
def baseEnd_270898 : Nat := 27476717499612117339095

theorem tailTrace_270898 : CollatzResearch.WordTrace tailWord_270898 prefixEnd_270898 27476717499612117339095 := by
  unfold tailWord_270898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470115443147571635027337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6586974515060191026739565 2470115443147571635027337)
  ·
    refine ⟨1852586582360678726270503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2470115443147571635027337 1852586582360678726270503)
    ·
      refine ⟨2778879873541018089405755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852586582360678726270503 2778879873541018089405755)
      ·
        refine ⟨4168319810311527134108633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778879873541018089405755 4168319810311527134108633)
        ·
          refine ⟨3126239857733645350581475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168319810311527134108633 3126239857733645350581475)
          ·
            refine ⟨4689359786600468025872213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126239857733645350581475 4689359786600468025872213)
            ·
              refine ⟨27476717499612117339095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4689359786600468025872213 27476717499612117339095)
              ·
                rfl

theorem cell19_270898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_270898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270898 prefixEnd_270898 := by exact prefixLift 270898
  have htrace : WordTrace (prefixWord ++ tailWord_270898) baseStart_270898 baseEnd_270898 := by
    simpa [prefixWord, tailWord_270898, baseEnd_270898] using wordTrace_append hprefix tailTrace_270898
  have hstable : (prefixWord ++ tailWord_270898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270898).length < 2 ^ (prefixWord ++ tailWord_270898).sum := by decide
  have hdescent : baseEnd_270898 < baseStart_270898 := by decide
  rcases family_descends (prefixWord ++ tailWord_270898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270917 : List Nat := [1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_270917 : Nat := 118140960795 + 270917 * 2 ^ 59
def prefixEnd_270917 : Nat := 4983230072969 + 3 ^ 40 * 270917 * 2
def baseEnd_270917 : Nat := 82435933910649937595011

theorem tailTrace_270917 : CollatzResearch.WordTrace tailWord_270917 prefixEnd_270917 82435933910649937595011 := by
  unfold tailWord_270917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9881154759521452785051005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6587436506347635190034003 9881154759521452785051005)
  ·
    refine ⟨3705433034820544794394127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9881154759521452785051005 3705433034820544794394127)
    ·
      refine ⟨5558149552230817191591191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705433034820544794394127 5558149552230817191591191)
      ·
        refine ⟨8337224328346225787386787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558149552230817191591191 8337224328346225787386787)
        ·
          refine ⟨12505836492519338681080181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8337224328346225787386787 12505836492519338681080181)
          ·
            refine ⟨1172422171173688001351267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12505836492519338681080181 1172422171173688001351267)
            ·
              refine ⟨1758633256760532002026901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172422171173688001351267 1758633256760532002026901)
              ·
                refine ⟨82435933910649937595011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1758633256760532002026901 82435933910649937595011)
                ·
                  rfl

theorem cell19_270917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_270917 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270917 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270917 prefixEnd_270917 := by exact prefixLift 270917
  have htrace : WordTrace (prefixWord ++ tailWord_270917) baseStart_270917 baseEnd_270917 := by
    simpa [prefixWord, tailWord_270917, baseEnd_270917] using wordTrace_append hprefix tailTrace_270917
  have hstable : (prefixWord ++ tailWord_270917).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270917).length < 2 ^ (prefixWord ++ tailWord_270917).sum := by decide
  have hdescent : baseEnd_270917 < baseStart_270917 := by decide
  rcases family_descends (prefixWord ++ tailWord_270917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270936 : List Nat := [2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_270936 : Nat := 118140960795 + 270936 * 2 ^ 59
def prefixEnd_270936 : Nat := 4983230072969 + 3 ^ 40 * 270936 * 2
def baseEnd_270936 : Nat := 82441715322463523172737

theorem tailTrace_270936 : CollatzResearch.WordTrace tailWord_270936 prefixEnd_270936 82441715322463523172737 := by
  unfold tailWord_270936
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940923873226309514996331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6587898497635079353328441 4940923873226309514996331)
  ·
    refine ⟨7411385809839464272494497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4940923873226309514996331 7411385809839464272494497)
    ·
      refine ⟨5558539357379598204370873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7411385809839464272494497 5558539357379598204370873)
      ·
        refine ⟨4168904518034698653278155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5558539357379598204370873 4168904518034698653278155)
        ·
          refine ⟨6253356777052047979917233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4168904518034698653278155 6253356777052047979917233)
          ·
            refine ⟨4690017582789035984937925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6253356777052047979917233 4690017582789035984937925)
            ·
              refine ⟨879378296772944247175861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4690017582789035984937925 879378296772944247175861)
              ·
                refine ⟨82441715322463523172737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879378296772944247175861 82441715322463523172737)
                ·
                  rfl

theorem cell19_270936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_270936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_270936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_270936 prefixEnd_270936 := by exact prefixLift 270936
  have htrace : WordTrace (prefixWord ++ tailWord_270936) baseStart_270936 baseEnd_270936 := by
    simpa [prefixWord, tailWord_270936, baseEnd_270936] using wordTrace_append hprefix tailTrace_270936
  have hstable : (prefixWord ++ tailWord_270936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270936).length < 2 ^ (prefixWord ++ tailWord_270936).sum := by decide
  have hdescent : baseEnd_270936 < baseStart_270936 := by decide
  rcases family_descends (prefixWord ++ tailWord_270936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271012 : List Nat := [2, 3, 1, 2, 2, 1, 8]
def baseStart_271012 : Nat := 118140960795 + 271012 * 2 ^ 59
def prefixEnd_271012 : Nat := 4983230072969 + 3 ^ 40 * 271012 * 2
def baseEnd_271012 : Nat := 27488280323239288494547

theorem tailTrace_271012 : CollatzResearch.WordTrace tailWord_271012 prefixEnd_271012 27488280323239288494547 := by
  unfold tailWord_271012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942309847088642004879645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6589746462784856006506193 4942309847088642004879645)
  ·
    refine ⟨1853366192658240751829867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4942309847088642004879645 1853366192658240751829867)
    ·
      refine ⟨2780049288987361127744801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853366192658240751829867 2780049288987361127744801)
      ·
        refine ⟨2085036966740520845808601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2780049288987361127744801 2085036966740520845808601)
        ·
          refine ⟨1563777725055390634356451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2085036966740520845808601 1563777725055390634356451)
          ·
            refine ⟨2345666587583085951534677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563777725055390634356451 2345666587583085951534677)
            ·
              refine ⟨27488280323239288494547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2345666587583085951534677 27488280323239288494547)
              ·
                rfl

theorem cell19_271012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_271012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271012 prefixEnd_271012 := by exact prefixLift 271012
  have htrace : WordTrace (prefixWord ++ tailWord_271012) baseStart_271012 baseEnd_271012 := by
    simpa [prefixWord, tailWord_271012, baseEnd_271012] using wordTrace_append hprefix tailTrace_271012
  have hstable : (prefixWord ++ tailWord_271012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271012).length < 2 ^ (prefixWord ++ tailWord_271012).sum := by decide
  have hdescent : baseEnd_271012 < baseStart_271012 := by decide
  rcases family_descends (prefixWord ++ tailWord_271012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271048 : List Nat := [2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_271048 : Nat := 118140960795 + 271048 * 2 ^ 59
def prefixEnd_271048 : Nat := 4983230072969 + 3 ^ 40 * 271048 * 2
def baseEnd_271048 : Nat := 82475795223680448683543

theorem tailTrace_271048 : CollatzResearch.WordTrace tailWord_271048 prefixEnd_271048 82475795223680448683543 := by
  unfold tailWord_271048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942966361023431079034899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6590621814697908105379865 4942966361023431079034899)
  ·
    refine ⟨7414449541535146618552349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4942966361023431079034899 7414449541535146618552349)
    ·
      refine ⟨2780418578075679981957131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7414449541535146618552349 2780418578075679981957131)
      ·
        refine ⟨4170627867113519972935697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780418578075679981957131 4170627867113519972935697)
        ·
          refine ⟨3127970900335139979701773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4170627867113519972935697 3127970900335139979701773)
          ·
            refine ⟨1172989087625677492388165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3127970900335139979701773 1172989087625677492388165)
            ·
              refine ⟨219935453929814529822781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1172989087625677492388165 219935453929814529822781)
              ·
                refine ⟨82475795223680448683543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219935453929814529822781 82475795223680448683543)
                ·
                  rfl

theorem cell19_271048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_271048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271048 prefixEnd_271048 := by exact prefixLift 271048
  have htrace : WordTrace (prefixWord ++ tailWord_271048) baseStart_271048 baseEnd_271048 := by
    simpa [prefixWord, tailWord_271048, baseEnd_271048] using wordTrace_append hprefix tailTrace_271048
  have hstable : (prefixWord ++ tailWord_271048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271048).length < 2 ^ (prefixWord ++ tailWord_271048).sum := by decide
  have hdescent : baseEnd_271048 < baseStart_271048 := by decide
  rcases family_descends (prefixWord ++ tailWord_271048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271086 : List Nat := [4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_271086 : Nat := 118140960795 + 271086 * 2 ^ 59
def prefixEnd_271086 : Nat := 4983230072969 + 3 ^ 40 * 271086 * 2
def baseEnd_271086 : Nat := 82487358047307619838995

theorem tailTrace_271086 : CollatzResearch.WordTrace tailWord_271086 prefixEnd_271086 82487358047307619838995 := by
  unfold tailWord_271086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235914836988649330994139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6591545797272796431968741 1235914836988649330994139)
  ·
    refine ⟨1853872255482973996491209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235914836988649330994139 1853872255482973996491209)
    ·
      refine ⟨1390404191612230497368407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1853872255482973996491209 1390404191612230497368407)
      ·
        refine ⟨2085606287418345746052611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390404191612230497368407 2085606287418345746052611)
        ·
          refine ⟨3128409431127518619078917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2085606287418345746052611 3128409431127518619078917)
          ·
            refine ⟨586576768336409741077297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3128409431127518619078917 586576768336409741077297)
            ·
              refine ⟨439932576252307305807973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586576768336409741077297 439932576252307305807973)
              ·
                refine ⟨82487358047307619838995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439932576252307305807973 82487358047307619838995)
                ·
                  rfl

theorem cell19_271086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_271086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271086 prefixEnd_271086 := by exact prefixLift 271086
  have htrace : WordTrace (prefixWord ++ tailWord_271086) baseStart_271086 baseEnd_271086 := by
    simpa [prefixWord, tailWord_271086, baseEnd_271086] using wordTrace_append hprefix tailTrace_271086
  have hstable : (prefixWord ++ tailWord_271086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271086).length < 2 ^ (prefixWord ++ tailWord_271086).sum := by decide
  have hdescent : baseEnd_271086 < baseStart_271086 := by decide
  rcases family_descends (prefixWord ++ tailWord_271086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271088 : List Nat := [2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_271088 : Nat := 118140960795 + 271088 * 2 ^ 59
def prefixEnd_271088 : Nat := 4983230072969 + 3 ^ 40 * 271088 * 2
def baseEnd_271088 : Nat := 82487966616972207794545

theorem tailTrace_271088 : CollatzResearch.WordTrace tailWord_271088 prefixEnd_271088 82487966616972207794545 := by
  unfold tailWord_271088
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943695820950974494762959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6591594427934632659683945 4943695820950974494762959)
  ·
    refine ⟨7415543731426461742144439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4943695820950974494762959 7415543731426461742144439)
    ·
      refine ⟨11123315597139692613216659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7415543731426461742144439 11123315597139692613216659)
      ·
        refine ⟨16684973395709538919824989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11123315597139692613216659 16684973395709538919824989)
        ·
          refine ⟨6256865023391077094934371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16684973395709538919824989 6256865023391077094934371)
          ·
            refine ⟨9385297535086615642401557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6256865023391077094934371 9385297535086615642401557)
            ·
              refine ⟨439935821957185108237573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9385297535086615642401557 439935821957185108237573)
              ·
                refine ⟨82487966616972207794545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439935821957185108237573 82487966616972207794545)
                ·
                  rfl

theorem cell19_271088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_271088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271088 prefixEnd_271088 := by exact prefixLift 271088
  have htrace : WordTrace (prefixWord ++ tailWord_271088) baseStart_271088 baseEnd_271088 := by
    simpa [prefixWord, tailWord_271088, baseEnd_271088] using wordTrace_append hprefix tailTrace_271088
  have hstable : (prefixWord ++ tailWord_271088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271088).length < 2 ^ (prefixWord ++ tailWord_271088).sum := by decide
  have hdescent : baseEnd_271088 < baseStart_271088 := by decide
  rcases family_descends (prefixWord ++ tailWord_271088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271122 : List Nat := [3, 2, 4, 1, 3, 6]
def baseStart_271122 : Nat := 118140960795 + 271122 * 2 ^ 59
def prefixEnd_271122 : Nat := 4983230072969 + 3 ^ 40 * 271122 * 2
def baseEnd_271122 : Nat := 9166479144585578115433

theorem tailTrace_271122 : CollatzResearch.WordTrace tailWord_271122 prefixEnd_271122 9166479144585578115433 := by
  unfold tailWord_271122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472157930944693199065905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6592421149185848530842413 2472157930944693199065905)
  ·
    refine ⟨1854118448208519899299429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2472157930944693199065905 1854118448208519899299429)
    ·
      refine ⟨347647209039097481118643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1854118448208519899299429 347647209039097481118643)
      ·
        refine ⟨521470813558646221677965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347647209039097481118643 521470813558646221677965)
        ·
          refine ⟨195551555084492333129237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521470813558646221677965 195551555084492333129237)
          ·
            refine ⟨9166479144585578115433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 195551555084492333129237 9166479144585578115433)
            ·
              rfl

theorem cell19_271122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_271122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271122 prefixEnd_271122 := by exact prefixLift 271122
  have htrace : WordTrace (prefixWord ++ tailWord_271122) baseStart_271122 baseEnd_271122 := by
    simpa [prefixWord, tailWord_271122, baseEnd_271122] using wordTrace_append hprefix tailTrace_271122
  have hstable : (prefixWord ++ tailWord_271122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271122).length < 2 ^ (prefixWord ++ tailWord_271122).sum := by decide
  have hdescent : baseEnd_271122 < baseStart_271122 := by decide
  rcases family_descends (prefixWord ++ tailWord_271122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271124 : List Nat := [2, 4, 4, 9]
def baseStart_271124 : Nat := 118140960795 + 271124 * 2 ^ 59
def prefixEnd_271124 : Nat := 4983230072969 + 3 ^ 40 * 271124 * 2
def baseEnd_271124 : Nat := 1018505195937466555487

theorem tailTrace_271124 : CollatzResearch.WordTrace tailWord_271124 prefixEnd_271124 1018505195937466555487 := by
  unfold tailWord_271124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4944352334885763568918213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6592469779847684758557617 4944352334885763568918213)
  ·
    refine ⟨927066062791080669172165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4944352334885763568918213 927066062791080669172165)
    ·
      refine ⟨173824886773327625469781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 927066062791080669172165 173824886773327625469781)
      ·
        refine ⟨1018505195937466555487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 173824886773327625469781 1018505195937466555487)
        ·
          rfl

theorem cell19_271124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 9].length) (baseStart_271124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271124 prefixEnd_271124 := by exact prefixLift 271124
  have htrace : WordTrace (prefixWord ++ tailWord_271124) baseStart_271124 baseEnd_271124 := by
    simpa [prefixWord, tailWord_271124, baseEnd_271124] using wordTrace_append hprefix tailTrace_271124
  have hstable : (prefixWord ++ tailWord_271124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271124).length < 2 ^ (prefixWord ++ tailWord_271124).sum := by decide
  have hdescent : baseEnd_271124 < baseStart_271124 := by decide
  rcases family_descends (prefixWord ++ tailWord_271124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271158 : List Nat := [5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_271158 : Nat := 118140960795 + 271158 * 2 ^ 59
def prefixEnd_271158 : Nat := 4983230072969 + 3 ^ 40 * 271158 * 2
def baseEnd_271158 : Nat := 82509266555232786238799

theorem tailTrace_271158 : CollatzResearch.WordTrace tailWord_271158 prefixEnd_271158 82509266555232786238799 := by
  unfold tailWord_271158
  simp only [CollatzResearch.WordTrace]
  refine ⟨618121546978021934035883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6593296501098900629716085 618121546978021934035883)
  ·
    refine ⟨927182320467032901053825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618121546978021934035883 927182320467032901053825)
    ·
      refine ⟨695386740350274675790369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927182320467032901053825 695386740350274675790369)
      ·
        refine ⟨521540055262706006842777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 695386740350274675790369 521540055262706006842777)
        ·
          refine ⟨391155041447029505132083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521540055262706006842777 391155041447029505132083)
          ·
            refine ⟨586732562170544257698125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391155041447029505132083 586732562170544257698125)
            ·
              refine ⟨220024710813954096636797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 586732562170544257698125 220024710813954096636797)
              ·
                refine ⟨82509266555232786238799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220024710813954096636797 82509266555232786238799)
                ·
                  rfl

theorem cell19_271158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_271158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271158 prefixEnd_271158 := by exact prefixLift 271158
  have htrace : WordTrace (prefixWord ++ tailWord_271158) baseStart_271158 baseEnd_271158 := by
    simpa [prefixWord, tailWord_271158, baseEnd_271158] using wordTrace_append hprefix tailTrace_271158
  have hstable : (prefixWord ++ tailWord_271158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271158).length < 2 ^ (prefixWord ++ tailWord_271158).sum := by decide
  have hdescent : baseEnd_271158 < baseStart_271158 := by decide
  rcases family_descends (prefixWord ++ tailWord_271158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271234 : List Nat := [3, 4, 2, 2, 1, 2, 5]
def baseStart_271234 : Nat := 118140960795 + 271234 * 2 ^ 59
def prefixEnd_271234 : Nat := 4983230072969 + 3 ^ 40 * 271234 * 2
def baseEnd_271234 : Nat := 27510797400829042849901

theorem tailTrace_271234 : CollatzResearch.WordTrace tailWord_271234 prefixEnd_271234 27510797400829042849901 := by
  unfold tailWord_271234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473179174843253981085189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6595144466248677282893837 2473179174843253981085189)
  ·
    refine ⟨463721095283110121453473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2473179174843253981085189 463721095283110121453473)
    ·
      refine ⟨347790821462332591090105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 463721095283110121453473 347790821462332591090105)
      ·
        refine ⟨260843116096749443317579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347790821462332591090105 260843116096749443317579)
        ·
          refine ⟨391264674145124164976369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260843116096749443317579 391264674145124164976369)
          ·
            refine ⟨293448505608843123732277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391264674145124164976369 293448505608843123732277)
            ·
              refine ⟨27510797400829042849901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 293448505608843123732277 27510797400829042849901)
              ·
                rfl

theorem cell19_271234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_271234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271234 prefixEnd_271234 := by exact prefixLift 271234
  have htrace : WordTrace (prefixWord ++ tailWord_271234) baseStart_271234 baseEnd_271234 := by
    simpa [prefixWord, tailWord_271234, baseEnd_271234] using wordTrace_append hprefix tailTrace_271234
  have hstable : (prefixWord ++ tailWord_271234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271234).length < 2 ^ (prefixWord ++ tailWord_271234).sum := by decide
  have hdescent : baseEnd_271234 < baseStart_271234 := by decide
  rcases family_descends (prefixWord ++ tailWord_271234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271240 : List Nat := [2, 1, 3, 3, 2, 1, 7]
def baseStart_271240 : Nat := 118140960795 + 271240 * 2 ^ 59
def prefixEnd_271240 : Nat := 4983230072969 + 3 ^ 40 * 271240 * 2
def baseEnd_271240 : Nat := 27511405970493630805451

theorem tailTrace_271240 : CollatzResearch.WordTrace tailWord_271240 prefixEnd_271240 27511405970493630805451 := by
  unfold tailWord_271240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946467768675639474529587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6595290358234185966039449 4946467768675639474529587)
  ·
    refine ⟨7419701653013459211794381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946467768675639474529587 7419701653013459211794381)
    ·
      refine ⟨2782388119880047204422893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7419701653013459211794381 2782388119880047204422893)
      ·
        refine ⟨1043395544955017701658585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2782388119880047204422893 1043395544955017701658585)
        ·
          refine ⟨782546658716263276243939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043395544955017701658585 782546658716263276243939)
          ·
            refine ⟨1173819988074394914365909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782546658716263276243939 1173819988074394914365909)
            ·
              refine ⟨27511405970493630805451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1173819988074394914365909 27511405970493630805451)
              ·
                rfl

theorem cell19_271240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_271240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271240 prefixEnd_271240 := by exact prefixLift 271240
  have htrace : WordTrace (prefixWord ++ tailWord_271240) baseStart_271240 baseEnd_271240 := by
    simpa [prefixWord, tailWord_271240, baseEnd_271240] using wordTrace_append hprefix tailTrace_271240
  have hstable : (prefixWord ++ tailWord_271240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271240).length < 2 ^ (prefixWord ++ tailWord_271240).sum := by decide
  have hdescent : baseEnd_271240 < baseStart_271240 := by decide
  rcases family_descends (prefixWord ++ tailWord_271240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271314 : List Nat := [3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_271314 : Nat := 118140960795 + 271314 * 2 ^ 59
def prefixEnd_271314 : Nat := 4983230072969 + 3 ^ 40 * 271314 * 2
def baseEnd_271314 : Nat := 82556734989070646771707

theorem tailTrace_271314 : CollatzResearch.WordTrace tailWord_271314 prefixEnd_271314 82556734989070646771707 := by
  unfold tailWord_271314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473908634770797396813249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6597089692722126391501997 2473908634770797396813249)
  ·
    refine ⟨1855431476078098047609937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2473908634770797396813249 1855431476078098047609937)
    ·
      refine ⟨1391573607058573535707453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1855431476078098047609937 1391573607058573535707453)
      ·
        refine ⟨521840102646965075890295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1391573607058573535707453 521840102646965075890295)
        ·
          refine ⟨782760153970447613835443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521840102646965075890295 782760153970447613835443)
          ·
            refine ⟨1174140230955671420753165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782760153970447613835443 1174140230955671420753165)
            ·
              refine ⟨440302586608376782782437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174140230955671420753165 440302586608376782782437)
              ·
                refine ⟨82556734989070646771707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440302586608376782782437 82556734989070646771707)
                ·
                  rfl

theorem cell19_271314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_271314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271314 prefixEnd_271314 := by exact prefixLift 271314
  have htrace : WordTrace (prefixWord ++ tailWord_271314) baseStart_271314 baseEnd_271314 := by
    simpa [prefixWord, tailWord_271314, baseEnd_271314] using wordTrace_append hprefix tailTrace_271314
  have hstable : (prefixWord ++ tailWord_271314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271314).length < 2 ^ (prefixWord ++ tailWord_271314).sum := by decide
  have hdescent : baseEnd_271314 < baseStart_271314 := by decide
  rcases family_descends (prefixWord ++ tailWord_271314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271388 : List Nat := [2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_271388 : Nat := 118140960795 + 271388 * 2 ^ 59
def prefixEnd_271388 : Nat := 4983230072969 + 3 ^ 40 * 271388 * 2
def baseEnd_271388 : Nat := 82579252066660401127061

theorem tailTrace_271388 : CollatzResearch.WordTrace tailWord_271388 prefixEnd_271388 82579252066660401127061 := by
  unfold tailWord_271388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4949166770407550112723409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6598889027210066816964545 4949166770407550112723409)
  ·
    refine ⟨3711875077805662584542557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4949166770407550112723409 3711875077805662584542557)
    ·
      refine ⟨1391953154177123469203459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3711875077805662584542557 1391953154177123469203459)
      ·
        refine ⟨2087929731265685203805189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391953154177123469203459 2087929731265685203805189)
        ·
          refine ⟨391486824612315975713473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2087929731265685203805189 391486824612315975713473)
          ·
            refine ⟨293615118459236981785105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391486824612315975713473 293615118459236981785105)
            ·
              refine ⟨220211338844427736338829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293615118459236981785105 220211338844427736338829)
              ·
                refine ⟨82579252066660401127061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220211338844427736338829 82579252066660401127061)
                ·
                  rfl

theorem cell19_271388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_271388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271388 prefixEnd_271388 := by exact prefixLift 271388
  have htrace : WordTrace (prefixWord ++ tailWord_271388) baseStart_271388 baseEnd_271388 := by
    simpa [prefixWord, tailWord_271388, baseEnd_271388] using wordTrace_append hprefix tailTrace_271388
  have hstable : (prefixWord ++ tailWord_271388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271388).length < 2 ^ (prefixWord ++ tailWord_271388).sum := by decide
  have hdescent : baseEnd_271388 < baseStart_271388 := by decide
  rcases family_descends (prefixWord ++ tailWord_271388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271546 : List Nat := [3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_271546 : Nat := 118140960795 + 271546 * 2 ^ 59
def prefixEnd_271546 : Nat := 4983230072969 + 3 ^ 40 * 271546 * 2
def baseEnd_271546 : Nat := 82627329070162849615519

theorem tailTrace_271546 : CollatzResearch.WordTrace tailWord_271546 prefixEnd_271546 82627329070162849615519 := by
  unfold tailWord_271546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476024068560673302424623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6602730849495128806465661 2476024068560673302424623)
  ·
    refine ⟨3714036102841009953636935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476024068560673302424623 3714036102841009953636935)
    ·
      refine ⟨5571054154261514930455403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714036102841009953636935 5571054154261514930455403)
      ·
        refine ⟨8356581231392272395683105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5571054154261514930455403 8356581231392272395683105)
        ·
          refine ⟨6267435923544204296762329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8356581231392272395683105 6267435923544204296762329)
          ·
            refine ⟨4700576942658153222571747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6267435923544204296762329 4700576942658153222571747)
            ·
              refine ⟨7050865413987229833857621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700576942658153222571747 7050865413987229833857621)
              ·
                refine ⟨82627329070162849615519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7050865413987229833857621 82627329070162849615519)
                ·
                  rfl

theorem cell19_271546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_271546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271546 prefixEnd_271546 := by exact prefixLift 271546
  have htrace : WordTrace (prefixWord ++ tailWord_271546) baseStart_271546 baseEnd_271546 := by
    simpa [prefixWord, tailWord_271546, baseEnd_271546] using wordTrace_append hprefix tailTrace_271546
  have hstable : (prefixWord ++ tailWord_271546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271546).length < 2 ^ (prefixWord ++ tailWord_271546).sum := by decide
  have hdescent : baseEnd_271546 < baseStart_271546 := by decide
  rcases family_descends (prefixWord ++ tailWord_271546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271584 : List Nat := [2, 1, 1, 3, 1, 4, 7]
def baseStart_271584 : Nat := 118140960795 + 271584 * 2 ^ 59
def prefixEnd_271584 : Nat := 4983230072969 + 3 ^ 40 * 271584 * 2
def baseEnd_271584 : Nat := 27546297297930006923657

theorem tailTrace_271584 : CollatzResearch.WordTrace tailWord_271584 prefixEnd_271584 27546297297930006923657 := by
  unfold tailWord_271584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952741124052512849790903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6603654832070017133054537 4952741124052512849790903)
  ·
    refine ⟨7429111686078769274686355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4952741124052512849790903 7429111686078769274686355)
    ·
      refine ⟨11143667529118153912029533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7429111686078769274686355 11143667529118153912029533)
      ·
        refine ⟨4178875323419307717011075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11143667529118153912029533 4178875323419307717011075)
        ·
          refine ⟨6268312985128961575516613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178875323419307717011075 6268312985128961575516613)
          ·
            refine ⟨1175308684711680295409365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6268312985128961575516613 1175308684711680295409365)
            ·
              refine ⟨27546297297930006923657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1175308684711680295409365 27546297297930006923657)
              ·
                rfl

theorem cell19_271584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_271584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271584 prefixEnd_271584 := by exact prefixLift 271584
  have htrace : WordTrace (prefixWord ++ tailWord_271584) baseStart_271584 baseEnd_271584 := by
    simpa [prefixWord, tailWord_271584, baseEnd_271584] using wordTrace_append hprefix tailTrace_271584
  have hstable : (prefixWord ++ tailWord_271584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271584).length < 2 ^ (prefixWord ++ tailWord_271584).sum := by decide
  have hdescent : baseEnd_271584 < baseStart_271584 := by decide
  rcases family_descends (prefixWord ++ tailWord_271584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271603 : List Nat := [1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_271603 : Nat := 118140960795 + 271603 * 2 ^ 59
def prefixEnd_271603 : Nat := 4983230072969 + 3 ^ 40 * 271603 * 2
def baseEnd_271603 : Nat := 82644673305603606348697

theorem tailTrace_271603 : CollatzResearch.WordTrace tailWord_271603 prefixEnd_271603 82644673305603606348697 := by
  unfold tailWord_271603
  simp only [CollatzResearch.WordTrace]
  refine ⟨9906175235036191944523463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6604116823357461296348975 9906175235036191944523463)
  ·
    refine ⟨14859262852554287916785195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9906175235036191944523463 14859262852554287916785195)
    ·
      refine ⟨22288894278831431875177793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14859262852554287916785195 22288894278831431875177793)
      ·
        refine ⟨16716670709123573906383345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22288894278831431875177793 16716670709123573906383345)
        ·
          refine ⟨12537503031842680429787509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16716670709123573906383345 12537503031842680429787509)
          ·
            refine ⟨1175390909235251290292579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12537503031842680429787509 1175390909235251290292579)
            ·
              refine ⟨1763086363852876935438869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175390909235251290292579 1763086363852876935438869)
              ·
                refine ⟨82644673305603606348697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1763086363852876935438869 82644673305603606348697)
                ·
                  rfl

theorem cell19_271603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_271603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271603 prefixEnd_271603 := by exact prefixLift 271603
  have htrace : WordTrace (prefixWord ++ tailWord_271603) baseStart_271603 baseEnd_271603 := by
    simpa [prefixWord, tailWord_271603, baseEnd_271603] using wordTrace_append hprefix tailTrace_271603
  have hstable : (prefixWord ++ tailWord_271603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271603).length < 2 ^ (prefixWord ++ tailWord_271603).sum := by decide
  have hdescent : baseEnd_271603 < baseStart_271603 := by decide
  rcases family_descends (prefixWord ++ tailWord_271603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271620 : List Nat := [2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_271620 : Nat := 118140960795 + 271620 * 2 ^ 59
def prefixEnd_271620 : Nat := 4983230072969 + 3 ^ 40 * 271620 * 2
def baseEnd_271620 : Nat := 82649846147752603970873

theorem tailTrace_271620 : CollatzResearch.WordTrace tailWord_271620 prefixEnd_271620 82649846147752603970873 := by
  unfold tailWord_271620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953397637987301923946157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6604530183983069231928209 4953397637987301923946157)
  ·
    refine ⟨1857524114245238221479809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4953397637987301923946157 1857524114245238221479809)
    ·
      refine ⟨1393143085683928666109857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1857524114245238221479809 1393143085683928666109857)
      ·
        refine ⟨1044857314262946499582393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393143085683928666109857 1044857314262946499582393)
        ·
          refine ⟨783642985697209874686795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044857314262946499582393 783642985697209874686795)
          ·
            refine ⟨1175464478545814812030193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783642985697209874686795 1175464478545814812030193)
            ·
              refine ⟨881598358909361109022645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175464478545814812030193 881598358909361109022645)
              ·
                refine ⟨82649846147752603970873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 881598358909361109022645 82649846147752603970873)
                ·
                  rfl

theorem cell19_271620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_271620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271620 prefixEnd_271620 := by exact prefixLift 271620
  have htrace : WordTrace (prefixWord ++ tailWord_271620) baseStart_271620 baseEnd_271620 := by
    simpa [prefixWord, tailWord_271620, baseEnd_271620] using wordTrace_append hprefix tailTrace_271620
  have hstable : (prefixWord ++ tailWord_271620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271620).length < 2 ^ (prefixWord ++ tailWord_271620).sum := by decide
  have hdescent : baseEnd_271620 < baseStart_271620 := by decide
  rcases family_descends (prefixWord ++ tailWord_271620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271656 : List Nat := [2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_271656 : Nat := 118140960795 + 271656 * 2 ^ 59
def prefixEnd_271656 : Nat := 4983230072969 + 3 ^ 40 * 271656 * 2
def baseEnd_271656 : Nat := 82660800401715187170775

theorem tailTrace_271656 : CollatzResearch.WordTrace tailWord_271656 prefixEnd_271656 82660800401715187170775 := by
  unfold tailWord_271656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954054151922090998101411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6605405535896121330801881 4954054151922090998101411)
  ·
    refine ⟨7431081227883136497152117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4954054151922090998101411 7431081227883136497152117)
    ·
      refine ⟨696663865114044046608011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7431081227883136497152117 696663865114044046608011)
      ·
        refine ⟨1044995797671066069912017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696663865114044046608011 1044995797671066069912017)
        ·
          refine ⟨783746848253299552434013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044995797671066069912017 783746848253299552434013)
          ·
            refine ⟨293905068094987332162755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 783746848253299552434013 293905068094987332162755)
            ·
              refine ⟨440857602142480998244133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293905068094987332162755 440857602142480998244133)
              ·
                refine ⟨82660800401715187170775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440857602142480998244133 82660800401715187170775)
                ·
                  rfl

theorem cell19_271656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_271656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271656 prefixEnd_271656 := by exact prefixLift 271656
  have htrace : WordTrace (prefixWord ++ tailWord_271656) baseStart_271656 baseEnd_271656 := by
    simpa [prefixWord, tailWord_271656, baseEnd_271656] using wordTrace_append hprefix tailTrace_271656
  have hstable : (prefixWord ++ tailWord_271656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271656).length < 2 ^ (prefixWord ++ tailWord_271656).sum := by decide
  have hdescent : baseEnd_271656 < baseStart_271656 := by decide
  rcases family_descends (prefixWord ++ tailWord_271656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271717 : List Nat := [1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_271717 : Nat := 118140960795 + 271717 * 2 ^ 59
def prefixEnd_271717 : Nat := 4983230072969 + 3 ^ 40 * 271717 * 2
def baseEnd_271717 : Nat := 82679361776485119815053

theorem tailTrace_271717 : CollatzResearch.WordTrace tailWord_271717 prefixEnd_271717 82679361776485119815053 := by
  unfold tailWord_271717
  simp only [CollatzResearch.WordTrace]
  refine ⟨9910333156623189414173405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6606888771082126276115603 9910333156623189414173405)
  ·
    refine ⟨3716374933733696030315027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9910333156623189414173405 3716374933733696030315027)
    ·
      refine ⟨5574562400600544045472541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716374933733696030315027 5574562400600544045472541)
      ·
        refine ⟨2090460900225204017052203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5574562400600544045472541 2090460900225204017052203)
        ·
          refine ⟨3135691350337806025578305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090460900225204017052203 3135691350337806025578305)
          ·
            refine ⟨2351768512753354519183729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3135691350337806025578305 2351768512753354519183729)
            ·
              refine ⟨1763826384565015889387797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351768512753354519183729 1763826384565015889387797)
              ·
                refine ⟨82679361776485119815053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1763826384565015889387797 82679361776485119815053)
                ·
                  rfl

theorem cell19_271717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_271717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271717 prefixEnd_271717 := by exact prefixLift 271717
  have htrace : WordTrace (prefixWord ++ tailWord_271717) baseStart_271717 baseEnd_271717 := by
    simpa [prefixWord, tailWord_271717, baseEnd_271717] using wordTrace_append hprefix tailTrace_271717
  have hstable : (prefixWord ++ tailWord_271717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271717).length < 2 ^ (prefixWord ++ tailWord_271717).sum := by decide
  have hdescent : baseEnd_271717 < baseStart_271717 := by decide
  rcases family_descends (prefixWord ++ tailWord_271717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271753 : List Nat := [1, 2, 1, 1, 7, 2, 5]
def baseStart_271753 : Nat := 118140960795 + 271753 * 2 ^ 59
def prefixEnd_271753 : Nat := 4983230072969 + 3 ^ 40 * 271753 * 2
def baseEnd_271753 : Nat := 27563438676815901004985

theorem tailTrace_271753 : CollatzResearch.WordTrace tailWord_271753 prefixEnd_271753 27563438676815901004985 := by
  unfold tailWord_271753
  simp only [CollatzResearch.WordTrace]
  refine ⟨9911646184492767562483913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6607764122995178374989275 9911646184492767562483913)
  ·
    refine ⟨7433734638369575671862935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9911646184492767562483913 7433734638369575671862935)
    ·
      refine ⟨11150601957554363507794403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7433734638369575671862935 11150601957554363507794403)
      ·
        refine ⟨16725902936331545261691605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11150601957554363507794403 16725902936331545261691605)
        ·
          refine ⟨392013350070270592070897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16725902936331545261691605 392013350070270592070897)
          ·
            refine ⟨294010012552702944053173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392013350070270592070897 294010012552702944053173)
            ·
              refine ⟨27563438676815901004985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 294010012552702944053173 27563438676815901004985)
              ·
                rfl

theorem cell19_271753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_271753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271753 prefixEnd_271753 := by exact prefixLift 271753
  have htrace : WordTrace (prefixWord ++ tailWord_271753) baseStart_271753 baseEnd_271753 := by
    simpa [prefixWord, tailWord_271753, baseEnd_271753] using wordTrace_append hprefix tailTrace_271753
  have hstable : (prefixWord ++ tailWord_271753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271753).length < 2 ^ (prefixWord ++ tailWord_271753).sum := by decide
  have hdescent : baseEnd_271753 < baseStart_271753 := by decide
  rcases family_descends (prefixWord ++ tailWord_271753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271793 : List Nat := [1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_271793 : Nat := 118140960795 + 271793 * 2 ^ 59
def prefixEnd_271793 : Nat := 4983230072969 + 3 ^ 40 * 271793 * 2
def baseEnd_271793 : Nat := 82702487423739462125957

theorem tailTrace_271793 : CollatzResearch.WordTrace tailWord_271793 prefixEnd_271793 82702487423739462125957 := by
  unfold tailWord_271793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9913105104347854393940033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6608736736231902929293355 9913105104347854393940033)
  ·
    refine ⟨7434828828260890795455025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9913105104347854393940033 7434828828260890795455025)
    ·
      refine ⟨5576121621195668096591269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7434828828260890795455025 5576121621195668096591269)
      ·
        refine ⟨1045522803974187768110863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5576121621195668096591269 1045522803974187768110863)
        ·
          refine ⟨1568284205961281652166295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045522803974187768110863 1568284205961281652166295)
          ·
            refine ⟨2352426308941922478249443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568284205961281652166295 2352426308941922478249443)
            ·
              refine ⟨3528639463412883717374165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352426308941922478249443 3528639463412883717374165)
              ·
                refine ⟨82702487423739462125957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3528639463412883717374165 82702487423739462125957)
                ·
                  rfl

theorem cell19_271793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_271793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271793 prefixEnd_271793 := by exact prefixLift 271793
  have htrace : WordTrace (prefixWord ++ tailWord_271793) baseStart_271793 baseEnd_271793 := by
    simpa [prefixWord, tailWord_271793, baseEnd_271793] using wordTrace_append hprefix tailTrace_271793
  have hstable : (prefixWord ++ tailWord_271793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271793).length < 2 ^ (prefixWord ++ tailWord_271793).sum := by decide
  have hdescent : baseEnd_271793 < baseStart_271793 := by decide
  rcases family_descends (prefixWord ++ tailWord_271793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271848 : List Nat := [2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_271848 : Nat := 118140960795 + 271848 * 2 ^ 59
def prefixEnd_271848 : Nat := 4983230072969 + 3 ^ 40 * 271848 * 2
def baseEnd_271848 : Nat := 82719223089515630903585

theorem tailTrace_271848 : CollatzResearch.WordTrace tailWord_271848 prefixEnd_271848 82719223089515630903585 := by
  unfold tailWord_271848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957555559574299393596099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6610074079432399191461465 4957555559574299393596099)
  ·
    refine ⟨7436333339361449090394149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4957555559574299393596099 7436333339361449090394149)
    ·
      refine ⟨1394312501130271704448903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7436333339361449090394149 1394312501130271704448903)
      ·
        refine ⟨2091468751695407556673355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394312501130271704448903 2091468751695407556673355)
        ·
          refine ⟨3137203127543111335010033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091468751695407556673355 3137203127543111335010033)
          ·
            refine ⟨2352902345657333501257525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3137203127543111335010033 2352902345657333501257525)
            ·
              refine ⟨220584594905375015742893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2352902345657333501257525 220584594905375015742893)
              ·
                refine ⟨82719223089515630903585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220584594905375015742893 82719223089515630903585)
                ·
                  rfl

theorem cell19_271848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_271848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271848 prefixEnd_271848 := by exact prefixLift 271848
  have htrace : WordTrace (prefixWord ++ tailWord_271848) baseStart_271848 baseEnd_271848 := by
    simpa [prefixWord, tailWord_271848, baseEnd_271848] using wordTrace_append hprefix tailTrace_271848
  have hstable : (prefixWord ++ tailWord_271848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271848).length < 2 ^ (prefixWord ++ tailWord_271848).sum := by decide
  have hdescent : baseEnd_271848 < baseStart_271848 := by decide
  rcases family_descends (prefixWord ++ tailWord_271848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271869 : List Nat := [1, 4, 1, 1, 1, 5, 6]
def baseStart_271869 : Nat := 118140960795 + 271869 * 2 ^ 59
def prefixEnd_271869 : Nat := 4983230072969 + 3 ^ 40 * 271869 * 2
def baseEnd_271869 : Nat := 27575204356997934812287

theorem tailTrace_271869 : CollatzResearch.WordTrace tailWord_271869 prefixEnd_271869 27575204356997934812287 := by
  unfold tailWord_271869
  simp only [CollatzResearch.WordTrace]
  refine ⟨9915877052072519373706661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6610584701381679582471107 9915877052072519373706661)
  ·
    refine ⟨1859226947263597382569999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9915877052072519373706661 1859226947263597382569999)
    ·
      refine ⟨2788840420895396073854999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859226947263597382569999 2788840420895396073854999)
      ·
        refine ⟨4183260631343094110782499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788840420895396073854999 4183260631343094110782499)
        ·
          refine ⟨6274890947014641166173749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183260631343094110782499 6274890947014641166173749)
          ·
            refine ⟨588271026282622609328789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6274890947014641166173749 588271026282622609328789)
            ·
              refine ⟨27575204356997934812287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 588271026282622609328789 27575204356997934812287)
              ·
                rfl

theorem cell19_271869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_271869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271869 prefixEnd_271869 := by exact prefixLift 271869
  have htrace : WordTrace (prefixWord ++ tailWord_271869) baseStart_271869 baseEnd_271869 := by
    simpa [prefixWord, tailWord_271869, baseEnd_271869] using wordTrace_append hprefix tailTrace_271869
  have hstable : (prefixWord ++ tailWord_271869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271869).length < 2 ^ (prefixWord ++ tailWord_271869).sum := by decide
  have hdescent : baseEnd_271869 < baseStart_271869 := by decide
  rcases family_descends (prefixWord ++ tailWord_271869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271905 : List Nat := [1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_271905 : Nat := 118140960795 + 271905 * 2 ^ 59
def prefixEnd_271905 : Nat := 4983230072969 + 3 ^ 40 * 271905 * 2
def baseEnd_271905 : Nat := 82736567324956387636763

theorem tailTrace_271905 : CollatzResearch.WordTrace tailWord_271905 prefixEnd_271905 82736567324956387636763 := by
  unfold tailWord_271905
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917190079942097522017169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6611460053294731681344779 9917190079942097522017169)
  ·
    refine ⟨7437892559956573141512877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9917190079942097522017169 7437892559956573141512877)
    ·
      refine ⟨2789209709983714928067329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7437892559956573141512877 2789209709983714928067329)
      ·
        refine ⟨2091907282487786196050497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789209709983714928067329 2091907282487786196050497)
        ·
          refine ⟨1568930461865839647037873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091907282487786196050497 1568930461865839647037873)
          ·
            refine ⟨1176697846399379735278405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568930461865839647037873 1176697846399379735278405)
            ·
              refine ⟨220630846199883700364701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1176697846399379735278405 220630846199883700364701)
              ·
                refine ⟨82736567324956387636763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220630846199883700364701 82736567324956387636763)
                ·
                  rfl

theorem cell19_271905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_271905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271905 prefixEnd_271905 := by exact prefixLift 271905
  have htrace : WordTrace (prefixWord ++ tailWord_271905) baseStart_271905 baseEnd_271905 := by
    simpa [prefixWord, tailWord_271905, baseEnd_271905] using wordTrace_append hprefix tailTrace_271905
  have hstable : (prefixWord ++ tailWord_271905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271905).length < 2 ^ (prefixWord ++ tailWord_271905).sum := by decide
  have hdescent : baseEnd_271905 < baseStart_271905 := by decide
  rcases family_descends (prefixWord ++ tailWord_271905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271943 : List Nat := [1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_271943 : Nat := 118140960795 + 271943 * 2 ^ 59
def prefixEnd_271943 : Nat := 4983230072969 + 3 ^ 40 * 271943 * 2
def baseEnd_271943 : Nat := 82748130148583558792215

theorem tailTrace_271943 : CollatzResearch.WordTrace tailWord_271943 prefixEnd_271943 82748130148583558792215 := by
  unfold tailWord_271943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918576053804430011900483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6612384035869620007933655 9918576053804430011900483)
  ·
    refine ⟨14877864080706645017850725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9918576053804430011900483 14877864080706645017850725)
    ·
      refine ⟨2789599515132495940847011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14877864080706645017850725 2789599515132495940847011)
      ·
        refine ⟨4184399272698743911270517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789599515132495940847011 4184399272698743911270517)
        ·
          refine ⟨392287431815507241681611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4184399272698743911270517 392287431815507241681611)
          ·
            refine ⟨588431147723260862522417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392287431815507241681611 588431147723260862522417)
            ·
              refine ⟨441323360792445646891813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588431147723260862522417 441323360792445646891813)
              ·
                refine ⟨82748130148583558792215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441323360792445646891813 82748130148583558792215)
                ·
                  rfl

theorem cell19_271943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_271943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271943 prefixEnd_271943 := by exact prefixLift 271943
  have htrace : WordTrace (prefixWord ++ tailWord_271943) baseStart_271943 baseEnd_271943 := by
    simpa [prefixWord, tailWord_271943, baseEnd_271943] using wordTrace_append hprefix tailTrace_271943
  have hstable : (prefixWord ++ tailWord_271943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271943).length < 2 ^ (prefixWord ++ tailWord_271943).sum := by decide
  have hdescent : baseEnd_271943 < baseStart_271943 := by decide
  rcases family_descends (prefixWord ++ tailWord_271943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271981 : List Nat := [1, 5, 1, 1, 5, 6]
def baseStart_271981 : Nat := 118140960795 + 271981 * 2 ^ 59
def prefixEnd_271981 : Nat := 4983230072969 + 3 ^ 40 * 271981 * 2
def baseEnd_271981 : Nat := 9195521441356747771963

theorem tailTrace_271981 : CollatzResearch.WordTrace tailWord_271981 prefixEnd_271981 9195521441356747771963 := by
  unfold tailWord_271981
  simp only [CollatzResearch.WordTrace]
  refine ⟨9919962027666762501783797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6613308018444508334522531 9919962027666762501783797)
  ·
    refine ⟨929996440093758984542231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9919962027666762501783797 929996440093758984542231)
    ·
      refine ⟨1394994660140638476813347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929996440093758984542231 1394994660140638476813347)
      ·
        refine ⟨2092491990210957715220021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394994660140638476813347 2092491990210957715220021)
        ·
          refine ⟨196171124082277285801877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2092491990210957715220021 196171124082277285801877)
          ·
            refine ⟨9195521441356747771963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 196171124082277285801877 9195521441356747771963)
            ·
              rfl

theorem cell19_271981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_271981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_271981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_271981 prefixEnd_271981 := by exact prefixLift 271981
  have htrace : WordTrace (prefixWord ++ tailWord_271981) baseStart_271981 baseEnd_271981 := by
    simpa [prefixWord, tailWord_271981, baseEnd_271981] using wordTrace_append hprefix tailTrace_271981
  have hstable : (prefixWord ++ tailWord_271981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271981).length < 2 ^ (prefixWord ++ tailWord_271981).sum := by decide
  have hdescent : baseEnd_271981 < baseStart_271981 := by decide
  rcases family_descends (prefixWord ++ tailWord_271981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272070 : List Nat := [6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_272070 : Nat := 118140960795 + 272070 * 2 ^ 59
def prefixEnd_272070 : Nat := 4983230072969 + 3 ^ 40 * 272070 * 2
def baseEnd_272070 : Nat := 82786774322284893969647

theorem tailTrace_272070 : CollatzResearch.WordTrace tailWord_272070 prefixEnd_272070 82786774322284893969647 := by
  unfold tailWord_272070
  simp only [CollatzResearch.WordTrace]
  refine ⟨310100253885760334430427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6615472082896220467849109 310100253885760334430427)
  ·
    refine ⟨465150380828640501645641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 310100253885760334430427 465150380828640501645641)
    ·
      refine ⟨348862785621480376234231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 465150380828640501645641 348862785621480376234231)
      ·
        refine ⟨523294178432220564351347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348862785621480376234231 523294178432220564351347)
        ·
          refine ⟨784941267648330846527021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523294178432220564351347 784941267648330846527021)
          ·
            refine ⟨294352975368124067447633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 784941267648330846527021 294352975368124067447633)
            ·
              refine ⟨220764731526093050585725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294352975368124067447633 220764731526093050585725)
              ·
                refine ⟨82786774322284893969647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220764731526093050585725 82786774322284893969647)
                ·
                  rfl

theorem cell19_272070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_272070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272070 prefixEnd_272070 := by exact prefixLift 272070
  have htrace : WordTrace (prefixWord ++ tailWord_272070) baseStart_272070 baseEnd_272070 := by
    simpa [prefixWord, tailWord_272070, baseEnd_272070] using wordTrace_append hprefix tailTrace_272070
  have hstable : (prefixWord ++ tailWord_272070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272070).length < 2 ^ (prefixWord ++ tailWord_272070).sum := by decide
  have hdescent : baseEnd_272070 < baseStart_272070 := by decide
  rcases family_descends (prefixWord ++ tailWord_272070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272074 : List Nat := [3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_272074 : Nat := 118140960795 + 272074 * 2 ^ 59
def prefixEnd_272074 : Nat := 4983230072969 + 3 ^ 40 * 272074 * 2
def baseEnd_272074 : Nat := 82787991461614069880747

theorem tailTrace_272074 : CollatzResearch.WordTrace tailWord_272074 prefixEnd_272074 82787991461614069880747 := by
  unfold tailWord_272074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480838504082459846229819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6615569344219892923279517 2480838504082459846229819)
  ·
    refine ⟨3721257756123689769344729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2480838504082459846229819 3721257756123689769344729)
    ·
      refine ⟨2790943317092767327008547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3721257756123689769344729 2790943317092767327008547)
      ·
        refine ⟨4186414975639150990512821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790943317092767327008547 4186414975639150990512821)
        ·
          refine ⟨392476403966170405360577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4186414975639150990512821 392476403966170405360577)
          ·
            refine ⟨294357302974627804020433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392476403966170405360577 294357302974627804020433)
            ·
              refine ⟨220767977230970853015325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294357302974627804020433 220767977230970853015325)
              ·
                refine ⟨82787991461614069880747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220767977230970853015325 82787991461614069880747)
                ·
                  rfl

theorem cell19_272074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_272074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272074 prefixEnd_272074 := by exact prefixLift 272074
  have htrace : WordTrace (prefixWord ++ tailWord_272074) baseStart_272074 baseEnd_272074 := by
    simpa [prefixWord, tailWord_272074, baseEnd_272074] using wordTrace_append hprefix tailTrace_272074
  have hstable : (prefixWord ++ tailWord_272074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272074).length < 2 ^ (prefixWord ++ tailWord_272074).sum := by decide
  have hdescent : baseEnd_272074 < baseStart_272074 := by decide
  rcases family_descends (prefixWord ++ tailWord_272074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272076 : List Nat := [2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_272076 : Nat := 118140960795 + 272076 * 2 ^ 59
def prefixEnd_272076 : Nat := 4983230072969 + 3 ^ 40 * 272076 * 2
def baseEnd_272076 : Nat := 82788600031278657836297

theorem tailTrace_272076 : CollatzResearch.WordTrace tailWord_272076 prefixEnd_272076 82788600031278657836297 := by
  unfold tailWord_272076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961713481161296863246041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6615617974881729150994721 4961713481161296863246041)
  ·
    refine ⟨3721285110870972647434531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4961713481161296863246041 3721285110870972647434531)
    ·
      refine ⟨5581927666306458971151797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721285110870972647434531 5581927666306458971151797)
      ·
        refine ⟨523305718716230528545481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5581927666306458971151797 523305718716230528545481)
        ·
          refine ⟨392479289037172896409111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523305718716230528545481 392479289037172896409111)
          ·
            refine ⟨588718933555759344613667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392479289037172896409111 588718933555759344613667)
            ·
              refine ⟨883078400333639016920501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588718933555759344613667 883078400333639016920501)
              ·
                refine ⟨82788600031278657836297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883078400333639016920501 82788600031278657836297)
                ·
                  rfl

theorem cell19_272076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_272076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272076 prefixEnd_272076 := by exact prefixLift 272076
  have htrace : WordTrace (prefixWord ++ tailWord_272076) baseStart_272076 baseEnd_272076 := by
    simpa [prefixWord, tailWord_272076, baseEnd_272076] using wordTrace_append hprefix tailTrace_272076
  have hstable : (prefixWord ++ tailWord_272076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272076).length < 2 ^ (prefixWord ++ tailWord_272076).sum := by decide
  have hdescent : baseEnd_272076 < baseStart_272076 := by decide
  rcases family_descends (prefixWord ++ tailWord_272076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272078 : List Nat := [4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_272078 : Nat := 118140960795 + 272078 * 2 ^ 59
def prefixEnd_272078 : Nat := 4983230072969 + 3 ^ 40 * 272078 * 2
def baseEnd_272078 : Nat := 82789208600943245791847

theorem tailTrace_272078 : CollatzResearch.WordTrace tailWord_272078 prefixEnd_272078 82789208600943245791847 := by
  unfold tailWord_272078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240437488539418508508111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6615666605543565378709925 1240437488539418508508111)
  ·
    refine ⟨1860656232809127762762167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1240437488539418508508111 1860656232809127762762167)
    ·
      refine ⟨2790984349213691644143251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860656232809127762762167 2790984349213691644143251)
      ·
        refine ⟨4186476523820537466214877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790984349213691644143251 4186476523820537466214877)
        ·
          refine ⟨1569928696432701549830579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4186476523820537466214877 1569928696432701549830579)
          ·
            refine ⟨2354893044649052324745869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569928696432701549830579 2354893044649052324745869)
            ·
              refine ⟨883084891743394621779701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2354893044649052324745869 883084891743394621779701)
              ·
                refine ⟨82789208600943245791847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883084891743394621779701 82789208600943245791847)
                ·
                  rfl

theorem cell19_272078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_272078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272078 prefixEnd_272078 := by exact prefixLift 272078
  have htrace : WordTrace (prefixWord ++ tailWord_272078) baseStart_272078 baseEnd_272078 := by
    simpa [prefixWord, tailWord_272078, baseEnd_272078] using wordTrace_append hprefix tailTrace_272078
  have hstable : (prefixWord ++ tailWord_272078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272078).length < 2 ^ (prefixWord ++ tailWord_272078).sum := by decide
  have hdescent : baseEnd_272078 < baseStart_272078 := by decide
  rcases family_descends (prefixWord ++ tailWord_272078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272093 : List Nat := [1, 4, 3, 3, 1, 2, 5]
def baseStart_272093 : Nat := 118140960795 + 272093 * 2 ^ 59
def prefixEnd_272093 : Nat := 4983230072969 + 3 ^ 40 * 272093 * 2
def baseEnd_272093 : Nat := 27597924291142551819491

theorem tailTrace_272093 : CollatzResearch.WordTrace tailWord_272093 prefixEnd_272093 27597924291142551819491 := by
  unfold tailWord_272093
  simp only [CollatzResearch.WordTrace]
  refine ⟨9924047003261005629860933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6616031335507337086573955 9924047003261005629860933)
  ·
    refine ⟨1860758813111438555598925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9924047003261005629860933 1860758813111438555598925)
    ·
      refine ⟨697784554916789458349597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1860758813111438555598925 697784554916789458349597)
      ·
        refine ⟨261669208093796046881099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 697784554916789458349597 261669208093796046881099)
        ·
          refine ⟨392503812140694070321649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261669208093796046881099 392503812140694070321649)
          ·
            refine ⟨294377859105520552741237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392503812140694070321649 294377859105520552741237)
            ·
              refine ⟨27597924291142551819491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 294377859105520552741237 27597924291142551819491)
              ·
                rfl

theorem cell19_272093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_272093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272093 prefixEnd_272093 := by exact prefixLift 272093
  have htrace : WordTrace (prefixWord ++ tailWord_272093) baseStart_272093 baseEnd_272093 := by
    simpa [prefixWord, tailWord_272093, baseEnd_272093] using wordTrace_append hprefix tailTrace_272093
  have hstable : (prefixWord ++ tailWord_272093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272093).length < 2 ^ (prefixWord ++ tailWord_272093).sum := by decide
  have hdescent : baseEnd_272093 < baseStart_272093 := by decide
  rcases family_descends (prefixWord ++ tailWord_272093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272148 : List Nat := [2, 4, 4, 1, 2, 6]
def baseStart_272148 : Nat := 118140960795 + 272148 * 2 ^ 59
def prefixEnd_272148 : Nat := 4983230072969 + 3 ^ 40 * 272148 * 2
def baseEnd_272148 : Nat := 9201167615467091581789

theorem tailTrace_272148 : CollatzResearch.WordTrace tailWord_272148 prefixEnd_272148 9201167615467091581789 := by
  unfold tailWord_272148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963026509030875011556549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6617368678707833348742065 4963026509030875011556549)
  ·
    refine ⟨930567470443289064666853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4963026509030875011556549 930567470443289064666853)
    ·
      refine ⟨174481400708116699625035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 930567470443289064666853 174481400708116699625035)
      ·
        refine ⟨261722101062175049437553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174481400708116699625035 261722101062175049437553)
        ·
          refine ⟨196291575796631287078165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261722101062175049437553 196291575796631287078165)
          ·
            refine ⟨9201167615467091581789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 196291575796631287078165 9201167615467091581789)
            ·
              rfl

theorem cell19_272148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_272148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272148 prefixEnd_272148 := by exact prefixLift 272148
  have htrace : WordTrace (prefixWord ++ tailWord_272148) baseStart_272148 baseEnd_272148 := by
    simpa [prefixWord, tailWord_272148, baseEnd_272148] using wordTrace_append hprefix tailTrace_272148
  have hstable : (prefixWord ++ tailWord_272148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272148).length < 2 ^ (prefixWord ++ tailWord_272148).sum := by decide
  have hdescent : baseEnd_272148 < baseStart_272148 := by decide
  rcases family_descends (prefixWord ++ tailWord_272148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272266 : List Nat := [3, 1, 2, 4, 2, 2, 5]
def baseStart_272266 : Nat := 118140960795 + 272266 * 2 ^ 59
def prefixEnd_272266 : Nat := 4983230072969 + 3 ^ 40 * 272266 * 2
def baseEnd_272266 : Nat := 27615471383138171204519

theorem tailTrace_272266 : CollatzResearch.WordTrace tailWord_272266 prefixEnd_272266 27615471383138171204519 := by
  unfold tailWord_272266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482589207908564043977163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6620237887756170783939101 2482589207908564043977163)
  ·
    refine ⟨3723883811862846065965745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2482589207908564043977163 3723883811862846065965745)
    ·
      refine ⟨2792912858897134549474309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3723883811862846065965745 2792912858897134549474309)
      ·
        refine ⟨523671161043212728026433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2792912858897134549474309 523671161043212728026433)
        ·
          refine ⟨392753370782409546019825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523671161043212728026433 392753370782409546019825)
          ·
            refine ⟨294565028086807159514869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392753370782409546019825 294565028086807159514869)
            ·
              refine ⟨27615471383138171204519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 294565028086807159514869 27615471383138171204519)
              ·
                rfl

theorem cell19_272266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_272266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272266 prefixEnd_272266 := by exact prefixLift 272266
  have htrace : WordTrace (prefixWord ++ tailWord_272266) baseStart_272266 baseEnd_272266 := by
    simpa [prefixWord, tailWord_272266, baseEnd_272266] using wordTrace_append hprefix tailTrace_272266
  have hstable : (prefixWord ++ tailWord_272266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272266).length < 2 ^ (prefixWord ++ tailWord_272266).sum := by decide
  have hdescent : baseEnd_272266 < baseStart_272266 := by decide
  rcases family_descends (prefixWord ++ tailWord_272266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272460 : List Nat := [2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_272460 : Nat := 118140960795 + 272460 * 2 ^ 59
def prefixEnd_272460 : Nat := 4983230072969 + 3 ^ 40 * 272460 * 2
def baseEnd_272460 : Nat := 82905445406879545301917

theorem tailTrace_272460 : CollatzResearch.WordTrace tailWord_272460 prefixEnd_272460 82905445406879545301917 := by
  unfold tailWord_272460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968716296465713654235417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6624955061954284872313889 4968716296465713654235417)
  ·
    refine ⟨3726537222349285240676563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4968716296465713654235417 3726537222349285240676563)
    ·
      refine ⟨5589805833523927861014845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726537222349285240676563 5589805833523927861014845)
      ·
        refine ⟨2096177187571472947880567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5589805833523927861014845 2096177187571472947880567)
        ·
          refine ⟨3144265781357209421820851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2096177187571472947880567 3144265781357209421820851)
          ·
            refine ⟨4716398672035814132731277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144265781357209421820851 4716398672035814132731277)
            ·
              refine ⟨1768649502013430299774229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4716398672035814132731277 1768649502013430299774229)
              ·
                refine ⟨82905445406879545301917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1768649502013430299774229 82905445406879545301917)
                ·
                  rfl

theorem cell19_272460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_272460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272460 prefixEnd_272460 := by exact prefixLift 272460
  have htrace : WordTrace (prefixWord ++ tailWord_272460) baseStart_272460 baseEnd_272460 := by
    simpa [prefixWord, tailWord_272460, baseEnd_272460] using wordTrace_append hprefix tailTrace_272460
  have hstable : (prefixWord ++ tailWord_272460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272460).length < 2 ^ (prefixWord ++ tailWord_272460).sum := by decide
  have hdescent : baseEnd_272460 < baseStart_272460 := by decide
  rcases family_descends (prefixWord ++ tailWord_272460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272498 : List Nat := [3, 2, 1, 2, 2, 9]
def baseStart_272498 : Nat := 118140960795 + 272498 * 2 ^ 59
def prefixEnd_272498 : Nat := 4983230072969 + 3 ^ 40 * 272498 * 2
def baseEnd_272498 : Nat := 9213000914500746273041

theorem tailTrace_272498 : CollatzResearch.WordTrace tailWord_272498 prefixEnd_272498 9213000914500746273041 := by
  unfold tailWord_272498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484704641698439949588537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6625879044529173198902765 2484704641698439949588537)
  ·
    refine ⟨1863528481273829962191403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2484704641698439949588537 1863528481273829962191403)
    ·
      refine ⟨2795292721910744943287105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863528481273829962191403 2795292721910744943287105)
      ·
        refine ⟨2096469541433058707465329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2795292721910744943287105 2096469541433058707465329)
        ·
          refine ⟨1572352156074794030598997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2096469541433058707465329 1572352156074794030598997)
          ·
            refine ⟨9213000914500746273041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1572352156074794030598997 9213000914500746273041)
            ·
              rfl

theorem cell19_272498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_272498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272498 prefixEnd_272498 := by exact prefixLift 272498
  have htrace : WordTrace (prefixWord ++ tailWord_272498) baseStart_272498 baseEnd_272498 := by
    simpa [prefixWord, tailWord_272498, baseEnd_272498] using wordTrace_append hprefix tailTrace_272498
  have hstable : (prefixWord ++ tailWord_272498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272498).length < 2 ^ (prefixWord ++ tailWord_272498).sum := by decide
  have hdescent : baseEnd_272498 < baseStart_272498 := by decide
  rcases family_descends (prefixWord ++ tailWord_272498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272513 : List Nat := [1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_272513 : Nat := 118140960795 + 272513 * 2 ^ 59
def prefixEnd_272513 : Nat := 4983230072969 + 3 ^ 40 * 272513 * 2
def baseEnd_272513 : Nat := 82921572502991126123995

theorem tailTrace_272513 : CollatzResearch.WordTrace tailWord_272513 prefixEnd_272513 82921572502991126123995 := by
  unfold tailWord_272513
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939365661739417360150193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626243774492944906766795 9939365661739417360150193)
  ·
    refine ⟨7454524246304563020112645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9939365661739417360150193 7454524246304563020112645)
    ·
      refine ⟨1397723296182105566271121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7454524246304563020112645 1397723296182105566271121)
      ·
        refine ⟨1048292472136579174703341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1397723296182105566271121 1048292472136579174703341)
        ·
          refine ⟨393109677051217190513753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1048292472136579174703341 393109677051217190513753)
          ·
            refine ⟨294832257788412892885315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393109677051217190513753 294832257788412892885315)
            ·
              refine ⟨442248386682619339327973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294832257788412892885315 442248386682619339327973)
              ·
                refine ⟨82921572502991126123995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442248386682619339327973 82921572502991126123995)
                ·
                  rfl

theorem cell19_272513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_272513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272513 prefixEnd_272513 := by exact prefixLift 272513
  have htrace : WordTrace (prefixWord ++ tailWord_272513) baseStart_272513 baseEnd_272513 := by
    simpa [prefixWord, tailWord_272513, baseEnd_272513] using wordTrace_append hprefix tailTrace_272513
  have hstable : (prefixWord ++ tailWord_272513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272513).length < 2 ^ (prefixWord ++ tailWord_272513).sum := by decide
  have hdescent : baseEnd_272513 < baseStart_272513 := by decide
  rcases family_descends (prefixWord ++ tailWord_272513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272515 : List Nat := [1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_272515 : Nat := 118140960795 + 272515 * 2 ^ 59
def prefixEnd_272515 : Nat := 4983230072969 + 3 ^ 40 * 272515 * 2
def baseEnd_272515 : Nat := 82922181072655714079545

theorem tailTrace_272515 : CollatzResearch.WordTrace tailWord_272515 prefixEnd_272515 82922181072655714079545 := by
  unfold tailWord_272515
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939438607732171701722999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626292405154781134481999 9939438607732171701722999)
  ·
    refine ⟨14909157911598257552584499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9939438607732171701722999 14909157911598257552584499)
    ·
      refine ⟨22363736867397386328876749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14909157911598257552584499 22363736867397386328876749)
      ·
        refine ⟨8386401325274019873328781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22363736867397386328876749 8386401325274019873328781)
        ·
          refine ⟨3144900496977757452498293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8386401325274019873328781 3144900496977757452498293)
          ·
            refine ⟨294834421591664761171715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3144900496977757452498293 294834421591664761171715)
            ·
              refine ⟨442251632387497141757573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294834421591664761171715 442251632387497141757573)
              ·
                refine ⟨82922181072655714079545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442251632387497141757573 82922181072655714079545)
                ·
                  rfl

theorem cell19_272515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_272515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272515 prefixEnd_272515 := by exact prefixLift 272515
  have htrace : WordTrace (prefixWord ++ tailWord_272515) baseStart_272515 baseEnd_272515 := by
    simpa [prefixWord, tailWord_272515, baseEnd_272515] using wordTrace_append hprefix tailTrace_272515
  have hstable : (prefixWord ++ tailWord_272515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272515).length < 2 ^ (prefixWord ++ tailWord_272515).sum := by decide
  have hdescent : baseEnd_272515 < baseStart_272515 := by decide
  rcases family_descends (prefixWord ++ tailWord_272515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272650 : List Nat := [3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_272650 : Nat := 118140960795 + 272650 * 2 ^ 59
def prefixEnd_272650 : Nat := 4983230072969 + 3 ^ 40 * 272650 * 2
def baseEnd_272650 : Nat := 82963259525015401079177

theorem tailTrace_272650 : CollatzResearch.WordTrace tailWord_272650 prefixEnd_272650 82963259525015401079177 := by
  unfold tailWord_272650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486090615560772439471851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6629574974828726505258269 2486090615560772439471851)
  ·
    refine ⟨3729135923341158659207777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486090615560772439471851 3729135923341158659207777)
    ·
      refine ⟨2796851942505868994405833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3729135923341158659207777 2796851942505868994405833)
      ·
        refine ⟨2097638956879401745804375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2796851942505868994405833 2097638956879401745804375)
        ·
          refine ⟨3146458435319102618706563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097638956879401745804375 3146458435319102618706563)
          ·
            refine ⟨4719687652978653928059845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146458435319102618706563 4719687652978653928059845)
            ·
              refine ⟨884941434933497611511221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4719687652978653928059845 884941434933497611511221)
              ·
                refine ⟨82963259525015401079177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 884941434933497611511221 82963259525015401079177)
                ·
                  rfl

theorem cell19_272650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_272650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272650 prefixEnd_272650 := by exact prefixLift 272650
  have htrace : WordTrace (prefixWord ++ tailWord_272650) baseStart_272650 baseEnd_272650 := by
    simpa [prefixWord, tailWord_272650, baseEnd_272650] using wordTrace_append hprefix tailTrace_272650
  have hstable : (prefixWord ++ tailWord_272650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272650).length < 2 ^ (prefixWord ++ tailWord_272650).sum := by decide
  have hdescent : baseEnd_272650 < baseStart_272650 := by decide
  rcases family_descends (prefixWord ++ tailWord_272650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272669 : List Nat := [1, 4, 2, 3, 9]
def baseStart_272669 : Nat := 118140960795 + 272669 * 2 ^ 59
def prefixEnd_272669 : Nat := 4983230072969 + 3 ^ 40 * 272669 * 2
def baseEnd_272669 : Nat := 3072927442104777283589

theorem tailTrace_272669 : CollatzResearch.WordTrace tailWord_272669 prefixEnd_272669 3072927442104777283589 := by
  unfold tailWord_272669
  simp only [CollatzResearch.WordTrace]
  refine ⟨9945055449174256002829061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6630036966116170668552707 9945055449174256002829061)
  ·
    refine ⟨1864697896720173000530449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9945055449174256002829061 1864697896720173000530449)
    ·
      refine ⟨1398523422540129750397837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1864697896720173000530449 1398523422540129750397837)
      ·
        refine ⟨524446283452548656399189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1398523422540129750397837 524446283452548656399189)
        ·
          refine ⟨3072927442104777283589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 524446283452548656399189 3072927442104777283589)
          ·
            rfl

theorem cell19_272669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 9].length) (baseStart_272669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272669 prefixEnd_272669 := by exact prefixLift 272669
  have htrace : WordTrace (prefixWord ++ tailWord_272669) baseStart_272669 baseEnd_272669 := by
    simpa [prefixWord, tailWord_272669, baseEnd_272669] using wordTrace_append hprefix tailTrace_272669
  have hstable : (prefixWord ++ tailWord_272669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272669).length < 2 ^ (prefixWord ++ tailWord_272669).sum := by decide
  have hdescent : baseEnd_272669 < baseStart_272669 := by decide
  rcases family_descends (prefixWord ++ tailWord_272669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272682 : List Nat := [3, 1, 4, 2, 3, 1, 1, 4]
def baseStart_272682 : Nat := 118140960795 + 272682 * 2 ^ 59
def prefixEnd_272682 : Nat := 4983230072969 + 3 ^ 40 * 272682 * 2
def baseEnd_272682 : Nat := 82972996639648808367979

theorem tailTrace_272682 : CollatzResearch.WordTrace tailWord_272682 prefixEnd_272682 82972996639648808367979 := by
  unfold tailWord_272682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486382399531789805763075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6630353065418106148701533 2486382399531789805763075)
  ·
    refine ⟨3729573599297684708644613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486382399531789805763075 3729573599297684708644613)
    ·
      refine ⟨699295049868315882870865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3729573599297684708644613 699295049868315882870865)
      ·
        refine ⟨524471287401236912153149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699295049868315882870865 524471287401236912153149)
        ·
          refine ⟨196676732775463842057431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 524471287401236912153149 196676732775463842057431)
          ·
            refine ⟨295015099163195763086147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196676732775463842057431 295015099163195763086147)
            ·
              refine ⟨442522648744793644629221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295015099163195763086147 442522648744793644629221)
              ·
                refine ⟨82972996639648808367979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442522648744793644629221 82972996639648808367979)
                ·
                  rfl

theorem cell19_272682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_272682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272682 prefixEnd_272682 := by exact prefixLift 272682
  have htrace : WordTrace (prefixWord ++ tailWord_272682) baseStart_272682 baseEnd_272682 := by
    simpa [prefixWord, tailWord_272682, baseEnd_272682] using wordTrace_append hprefix tailTrace_272682
  have hstable : (prefixWord ++ tailWord_272682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272682).length < 2 ^ (prefixWord ++ tailWord_272682).sum := by decide
  have hdescent : baseEnd_272682 < baseStart_272682 := by decide
  rcases family_descends (prefixWord ++ tailWord_272682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272798 : List Nat := [4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_272798 : Nat := 118140960795 + 272798 * 2 ^ 59
def prefixEnd_272798 : Nat := 4983230072969 + 3 ^ 40 * 272798 * 2
def baseEnd_272798 : Nat := 83008293680194909789885

theorem tailTrace_272798 : CollatzResearch.WordTrace tailWord_272798 prefixEnd_272798 83008293680194909789885 := by
  unfold tailWord_272798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1243720058213363879284381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6633173643804607356183365 1243720058213363879284381)
  ·
    refine ⟨466395021830011454731643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1243720058213363879284381 466395021830011454731643)
    ·
      refine ⟨699592532745017182097465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466395021830011454731643 699592532745017182097465)
      ·
        refine ⟨524694399558762886573099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699592532745017182097465 524694399558762886573099)
        ·
          refine ⟨787041599338144329859649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524694399558762886573099 787041599338144329859649)
          ·
            refine ⟨590281199503608247394737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787041599338144329859649 590281199503608247394737)
            ·
              refine ⟨442710899627706185546053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590281199503608247394737 442710899627706185546053)
              ·
                refine ⟨83008293680194909789885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442710899627706185546053 83008293680194909789885)
                ·
                  rfl

theorem cell19_272798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_272798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272798 prefixEnd_272798 := by exact prefixLift 272798
  have htrace : WordTrace (prefixWord ++ tailWord_272798) baseStart_272798 baseEnd_272798 := by
    simpa [prefixWord, tailWord_272798, baseEnd_272798] using wordTrace_append hprefix tailTrace_272798
  have hstable : (prefixWord ++ tailWord_272798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272798).length < 2 ^ (prefixWord ++ tailWord_272798).sum := by decide
  have hdescent : baseEnd_272798 < baseStart_272798 := by decide
  rcases family_descends (prefixWord ++ tailWord_272798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272897 : List Nat := [1, 2, 4, 1, 3, 2, 6]
def baseStart_272897 : Nat := 118140960795 + 272897 * 2 ^ 59
def prefixEnd_272897 : Nat := 4983230072969 + 3 ^ 40 * 272897 * 2
def baseEnd_272897 : Nat := 27679472626197337863205

theorem tailTrace_272897 : CollatzResearch.WordTrace tailWord_272897 prefixEnd_272897 27679472626197337863205 := by
  unfold tailWord_272897
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953371292348250942128945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6635580861565500628085963 9953371292348250942128945)
  ·
    refine ⟨7465028469261188206596709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9953371292348250942128945 7465028469261188206596709)
    ·
      refine ⟨1399692837986472788736883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7465028469261188206596709 1399692837986472788736883)
      ·
        refine ⟨2099539256979709183105325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399692837986472788736883 2099539256979709183105325)
        ·
          refine ⟨787327221367390943664497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2099539256979709183105325 787327221367390943664497)
          ·
            refine ⟨590495416025543207748373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787327221367390943664497 590495416025543207748373)
            ·
              refine ⟨27679472626197337863205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 590495416025543207748373 27679472626197337863205)
              ·
                rfl

theorem cell19_272897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_272897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272897 prefixEnd_272897 := by exact prefixLift 272897
  have htrace : WordTrace (prefixWord ++ tailWord_272897) baseStart_272897 baseEnd_272897 := by
    simpa [prefixWord, tailWord_272897, baseEnd_272897] using wordTrace_append hprefix tailTrace_272897
  have hstable : (prefixWord ++ tailWord_272897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272897).length < 2 ^ (prefixWord ++ tailWord_272897).sum := by decide
  have hdescent : baseEnd_272897 < baseStart_272897 := by decide
  rcases family_descends (prefixWord ++ tailWord_272897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272899 : List Nat := [1, 1, 1, 3, 2, 1, 10]
def baseStart_272899 : Nat := 118140960795 + 272899 * 2 ^ 59
def prefixEnd_272899 : Nat := 4983230072969 + 3 ^ 40 * 272899 * 2
def baseEnd_272899 : Nat := 27679675482752200515055

theorem tailTrace_272899 : CollatzResearch.WordTrace tailWord_272899 prefixEnd_272899 27679675482752200515055 := by
  unfold tailWord_272899
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953444238341005283701751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6635629492227336855801167 9953444238341005283701751)
  ·
    refine ⟨14930166357511507925552627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9953444238341005283701751 14930166357511507925552627)
    ·
      refine ⟨22395249536267261888328941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14930166357511507925552627 22395249536267261888328941)
      ·
        refine ⟨8398218576100223208123353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22395249536267261888328941 8398218576100223208123353)
        ·
          refine ⟨6298663932075167406092515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8398218576100223208123353 6298663932075167406092515)
          ·
            refine ⟨9447995898112751109138773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6298663932075167406092515 9447995898112751109138773)
            ·
              refine ⟨27679675482752200515055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9447995898112751109138773 27679675482752200515055)
              ·
                rfl

theorem cell19_272899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_272899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272899 prefixEnd_272899 := by exact prefixLift 272899
  have htrace : WordTrace (prefixWord ++ tailWord_272899) baseStart_272899 baseEnd_272899 := by
    simpa [prefixWord, tailWord_272899, baseEnd_272899] using wordTrace_append hprefix tailTrace_272899
  have hstable : (prefixWord ++ tailWord_272899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272899).length < 2 ^ (prefixWord ++ tailWord_272899).sum := by decide
  have hdescent : baseEnd_272899 < baseStart_272899 := by decide
  rcases family_descends (prefixWord ++ tailWord_272899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272948 : List Nat := [2, 5, 1, 3, 2, 1, 5]
def baseStart_272948 : Nat := 118140960795 + 272948 * 2 ^ 59
def prefixEnd_272948 : Nat := 4983230072969 + 3 ^ 40 * 272948 * 2
def baseEnd_272948 : Nat := 27684645468346335485381

theorem tailTrace_272948 : CollatzResearch.WordTrace tailWord_272948 prefixEnd_272948 27684645468346335485381 := by
  unfold tailWord_272948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977615707581743326117749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6636820943442324434823665 4977615707581743326117749)
  ·
    refine ⟨466651472585788436823539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4977615707581743326117749 466651472585788436823539)
    ·
      refine ⟨699977208878682655235309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466651472585788436823539 699977208878682655235309)
      ·
        refine ⟨262491453329505995713241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 699977208878682655235309 262491453329505995713241)
        ·
          refine ⟨196868589997129496784931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262491453329505995713241 196868589997129496784931)
          ·
            refine ⟨295302884995694245177397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196868589997129496784931 295302884995694245177397)
            ·
              refine ⟨27684645468346335485381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 295302884995694245177397 27684645468346335485381)
              ·
                rfl

theorem cell19_272948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_272948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272948 prefixEnd_272948 := by exact prefixLift 272948
  have htrace : WordTrace (prefixWord ++ tailWord_272948) baseStart_272948 baseEnd_272948 := by
    simpa [prefixWord, tailWord_272948, baseEnd_272948] using wordTrace_append hprefix tailTrace_272948
  have hstable : (prefixWord ++ tailWord_272948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272948).length < 2 ^ (prefixWord ++ tailWord_272948).sum := by decide
  have hdescent : baseEnd_272948 < baseStart_272948 := by decide
  rcases family_descends (prefixWord ++ tailWord_272948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272954 : List Nat := [3, 1, 1, 1, 3, 5, 5]
def baseStart_272954 : Nat := 118140960795 + 272954 * 2 ^ 59
def prefixEnd_272954 : Nat := 4983230072969 + 3 ^ 40 * 272954 * 2
def baseEnd_272954 : Nat := 27685254038010923440931

theorem tailTrace_272954 : CollatzResearch.WordTrace tailWord_272954 prefixEnd_272954 27685254038010923440931 := by
  unfold tailWord_272954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488862563285437419238479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6636966835427833117969277 2488862563285437419238479)
  ·
    refine ⟨3733293844928156128857719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2488862563285437419238479 3733293844928156128857719)
    ·
      refine ⟨5599940767392234193286579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3733293844928156128857719 5599940767392234193286579)
      ·
        refine ⟨8399911151088351289929869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599940767392234193286579 8399911151088351289929869)
        ·
          refine ⟨3149966681658131733723701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8399911151088351289929869 3149966681658131733723701)
          ·
            refine ⟨295309376405449850036597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3149966681658131733723701 295309376405449850036597)
            ·
              refine ⟨27685254038010923440931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 295309376405449850036597 27685254038010923440931)
              ·
                rfl

theorem cell19_272954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_272954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272954 prefixEnd_272954 := by exact prefixLift 272954
  have htrace : WordTrace (prefixWord ++ tailWord_272954) baseStart_272954 baseEnd_272954 := by
    simpa [prefixWord, tailWord_272954, baseEnd_272954] using wordTrace_append hprefix tailTrace_272954
  have hstable : (prefixWord ++ tailWord_272954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272954).length < 2 ^ (prefixWord ++ tailWord_272954).sum := by decide
  have hdescent : baseEnd_272954 < baseStart_272954 := by decide
  rcases family_descends (prefixWord ++ tailWord_272954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272975 : List Nat := [1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_272975 : Nat := 118140960795 + 272975 * 2 ^ 59
def prefixEnd_272975 : Nat := 4983230072969 + 3 ^ 40 * 272975 * 2
def baseEnd_272975 : Nat := 83062152095510943856069

theorem tailTrace_272975 : CollatzResearch.WordTrace tailWord_272975 prefixEnd_272975 83062152095510943856069 := by
  unfold tailWord_272975
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956216186065670263468379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637477457377113508978919 9956216186065670263468379)
  ·
    refine ⟨14934324279098505395202569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9956216186065670263468379 14934324279098505395202569)
    ·
      refine ⟨11200743209323879046401927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14934324279098505395202569 11200743209323879046401927)
      ·
        refine ⟨16801114813985818569602891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11200743209323879046401927 16801114813985818569602891)
        ·
          refine ⟨25201672220978727854404337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16801114813985818569602891 25201672220978727854404337)
          ·
            refine ⟨18901254165734045890803253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25201672220978727854404337 18901254165734045890803253)
            ·
              refine ⟨1771992578037566802262805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18901254165734045890803253 1771992578037566802262805)
              ·
                refine ⟨83062152095510943856069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1771992578037566802262805 83062152095510943856069)
                ·
                  rfl

theorem cell19_272975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_272975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_272975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_272975 prefixEnd_272975 := by exact prefixLift 272975
  have htrace : WordTrace (prefixWord ++ tailWord_272975) baseStart_272975 baseEnd_272975 := by
    simpa [prefixWord, tailWord_272975, baseEnd_272975] using wordTrace_append hprefix tailTrace_272975
  have hstable : (prefixWord ++ tailWord_272975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272975).length < 2 ^ (prefixWord ++ tailWord_272975).sum := by decide
  have hdescent : baseEnd_272975 < baseStart_272975 := by decide
  rcases family_descends (prefixWord ++ tailWord_272975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273028 : List Nat := [2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_273028 : Nat := 118140960795 + 273028 * 2 ^ 59
def prefixEnd_273028 : Nat := 4983230072969 + 3 ^ 40 * 273028 * 2
def baseEnd_273028 : Nat := 83078279191622524678147

theorem tailTrace_273028 : CollatzResearch.WordTrace tailWord_273028 prefixEnd_273028 83078279191622524678147 := by
  unfold tailWord_273028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979074627436830157573869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6638766169915773543431825 4979074627436830157573869)
  ·
    refine ⟨1867152985288811309090201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4979074627436830157573869 1867152985288811309090201)
    ·
      refine ⟨1400364738966608481817651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1867152985288811309090201 1400364738966608481817651)
      ·
        refine ⟨2100547108449912722726477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400364738966608481817651 2100547108449912722726477)
        ·
          refine ⟨787705165668717271022429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2100547108449912722726477 787705165668717271022429)
          ·
            refine ⟨295389437125768976633411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 787705165668717271022429 295389437125768976633411)
            ·
              refine ⟨443084155688653464950117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295389437125768976633411 443084155688653464950117)
              ·
                refine ⟨83078279191622524678147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443084155688653464950117 83078279191622524678147)
                ·
                  rfl

theorem cell19_273028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_273028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273028 prefixEnd_273028 := by exact prefixLift 273028
  have htrace : WordTrace (prefixWord ++ tailWord_273028) baseStart_273028 baseEnd_273028 := by
    simpa [prefixWord, tailWord_273028, baseEnd_273028] using wordTrace_append hprefix tailTrace_273028
  have hstable : (prefixWord ++ tailWord_273028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273028).length < 2 ^ (prefixWord ++ tailWord_273028).sum := by decide
  have hdescent : baseEnd_273028 < baseStart_273028 := by decide
  rcases family_descends (prefixWord ++ tailWord_273028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273049 : List Nat := [1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_273049 : Nat := 118140960795 + 273049 * 2 ^ 59
def prefixEnd_273049 : Nat := 4983230072969 + 3 ^ 40 * 273049 * 2
def baseEnd_273049 : Nat := 83084669173100698211423

theorem tailTrace_273049 : CollatzResearch.WordTrace tailWord_273049 prefixEnd_273049 83084669173100698211423 := by
  unfold tailWord_273049
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958915187797580901662201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6639276791865053934441467 9958915187797580901662201)
  ·
    refine ⟨7469186390848185676246651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9958915187797580901662201 7469186390848185676246651)
    ·
      refine ⟨11203779586272278514369977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7469186390848185676246651 11203779586272278514369977)
      ·
        refine ⟨8402834689704208885777483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11203779586272278514369977 8402834689704208885777483)
        ·
          refine ⟨12604252034556313328666225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8402834689704208885777483 12604252034556313328666225)
          ·
            refine ⟨9453189025917234996499669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12604252034556313328666225 9453189025917234996499669)
            ·
              refine ⟨221559117794935195230461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9453189025917234996499669 221559117794935195230461)
              ·
                refine ⟨83084669173100698211423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221559117794935195230461 83084669173100698211423)
                ·
                  rfl

theorem cell19_273049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_273049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273049 prefixEnd_273049 := by exact prefixLift 273049
  have htrace : WordTrace (prefixWord ++ tailWord_273049) baseStart_273049 baseEnd_273049 := by
    simpa [prefixWord, tailWord_273049, baseEnd_273049] using wordTrace_append hprefix tailTrace_273049
  have hstable : (prefixWord ++ tailWord_273049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273049).length < 2 ^ (prefixWord ++ tailWord_273049).sum := by decide
  have hdescent : baseEnd_273049 < baseStart_273049 := by decide
  rcases family_descends (prefixWord ++ tailWord_273049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273125 : List Nat := [1, 3, 1, 4, 1, 4, 5]
def baseStart_273125 : Nat := 118140960795 + 273125 * 2 ^ 59
def prefixEnd_273125 : Nat := 4983230072969 + 3 ^ 40 * 273125 * 2
def baseEnd_273125 : Nat := 27702598273451680174109

theorem tailTrace_273125 : CollatzResearch.WordTrace tailWord_273125 prefixEnd_273125 27702598273451680174109 := by
  unfold tailWord_273125
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961687135522245881428829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6641124757014830587619219 9961687135522245881428829)
  ·
    refine ⟨3735632675820842205535811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9961687135522245881428829 3735632675820842205535811)
    ·
      refine ⟨5603449013731263308303717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3735632675820842205535811 5603449013731263308303717)
      ·
        refine ⟨1050646690074611870306947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5603449013731263308303717 1050646690074611870306947)
        ·
          refine ⟨1575970035111917805460421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050646690074611870306947 1575970035111917805460421)
          ·
            refine ⟨295494381583484588523829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1575970035111917805460421 295494381583484588523829)
            ·
              refine ⟨27702598273451680174109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 295494381583484588523829 27702598273451680174109)
              ·
                rfl

theorem cell19_273125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_273125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273125 prefixEnd_273125 := by exact prefixLift 273125
  have htrace : WordTrace (prefixWord ++ tailWord_273125) baseStart_273125 baseEnd_273125 := by
    simpa [prefixWord, tailWord_273125, baseEnd_273125] using wordTrace_append hprefix tailTrace_273125
  have hstable : (prefixWord ++ tailWord_273125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273125).length < 2 ^ (prefixWord ++ tailWord_273125).sum := by decide
  have hdescent : baseEnd_273125 < baseStart_273125 := by decide
  rcases family_descends (prefixWord ++ tailWord_273125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273146 : List Nat := [3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_273146 : Nat := 118140960795 + 273146 * 2 ^ 59
def prefixEnd_273146 : Nat := 4983230072969 + 3 ^ 40 * 273146 * 2
def baseEnd_273146 : Nat := 83114184801833214055603

theorem tailTrace_273146 : CollatzResearch.WordTrace tailWord_273146 prefixEnd_273146 83114184801833214055603 := by
  unfold tailWord_273146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490613267111541616985823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6641635378964110978628861 2490613267111541616985823)
  ·
    refine ⟨3735919900667312425478735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490613267111541616985823 3735919900667312425478735)
    ·
      refine ⟨5603879851000968638218103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3735919900667312425478735 5603879851000968638218103)
      ·
        refine ⟨8405819776501452957327155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5603879851000968638218103 8405819776501452957327155)
        ·
          refine ⟨12608729664752179435990733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8405819776501452957327155 12608729664752179435990733)
          ·
            refine ⟨4728273624282067288496525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12608729664752179435990733 4728273624282067288496525)
            ·
              refine ⟨1773102609105775233186197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4728273624282067288496525 1773102609105775233186197)
              ·
                refine ⟨83114184801833214055603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1773102609105775233186197 83114184801833214055603)
                ·
                  rfl

theorem cell19_273146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_273146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273146 prefixEnd_273146 := by exact prefixLift 273146
  have htrace : WordTrace (prefixWord ++ tailWord_273146) baseStart_273146 baseEnd_273146 := by
    simpa [prefixWord, tailWord_273146, baseEnd_273146] using wordTrace_append hprefix tailTrace_273146
  have hstable : (prefixWord ++ tailWord_273146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273146).length < 2 ^ (prefixWord ++ tailWord_273146).sum := by decide
  have hdescent : baseEnd_273146 < baseStart_273146 := by decide
  rcases family_descends (prefixWord ++ tailWord_273146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273182 : List Nat := [4, 3, 2, 10]
def baseStart_273182 : Nat := 118140960795 + 273182 * 2 ^ 59
def prefixEnd_273182 : Nat := 4983230072969 + 3 ^ 40 * 273182 * 2
def baseEnd_273182 : Nat := 1026236284639454287105

theorem tailTrace_273182 : CollatzResearch.WordTrace tailWord_273182 prefixEnd_273182 1026236284639454287105 := by
  unfold tailWord_273182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245470762039468077031725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6642510730877163077502533 1245470762039468077031725)
  ·
    refine ⟨467051535764800528886897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1245470762039468077031725 467051535764800528886897)
    ·
      refine ⟨350288651823600396665173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 467051535764800528886897 350288651823600396665173)
      ·
        refine ⟨1026236284639454287105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 350288651823600396665173 1026236284639454287105)
        ·
          rfl

theorem cell19_273182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 10].length) (baseStart_273182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273182 prefixEnd_273182 := by exact prefixLift 273182
  have htrace : WordTrace (prefixWord ++ tailWord_273182) baseStart_273182 baseEnd_273182 := by
    simpa [prefixWord, tailWord_273182, baseEnd_273182] using wordTrace_append hprefix tailTrace_273182
  have hstable : (prefixWord ++ tailWord_273182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273182).length < 2 ^ (prefixWord ++ tailWord_273182).sum := by decide
  have hdescent : baseEnd_273182 < baseStart_273182 := by decide
  rcases family_descends (prefixWord ++ tailWord_273182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273184 : List Nat := [2, 1, 1, 5, 1, 9]
def baseStart_273184 : Nat := 118140960795 + 273184 * 2 ^ 59
def prefixEnd_273184 : Nat := 4983230072969 + 3 ^ 40 * 273184 * 2
def baseEnd_273184 : Nat := 9236194180606709467895

theorem tailTrace_273184 : CollatzResearch.WordTrace tailWord_273184 prefixEnd_273184 9236194180606709467895 := by
  unfold tailWord_273184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981919521154249478913303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6642559361538999305217737 4981919521154249478913303)
  ·
    refine ⟨7472879281731374218369955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981919521154249478913303 7472879281731374218369955)
    ·
      refine ⟨11209318922597061327554933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7472879281731374218369955 11209318922597061327554933)
      ·
        refine ⟨1050873648993474499458275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11209318922597061327554933 1050873648993474499458275)
        ·
          refine ⟨1576310473490211749187413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050873648993474499458275 1576310473490211749187413)
          ·
            refine ⟨9236194180606709467895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1576310473490211749187413 9236194180606709467895)
            ·
              rfl

theorem cell19_273184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_273184 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273184 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273184 prefixEnd_273184 := by exact prefixLift 273184
  have htrace : WordTrace (prefixWord ++ tailWord_273184) baseStart_273184 baseEnd_273184 := by
    simpa [prefixWord, tailWord_273184, baseEnd_273184] using wordTrace_append hprefix tailTrace_273184
  have hstable : (prefixWord ++ tailWord_273184).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273184).length < 2 ^ (prefixWord ++ tailWord_273184).sum := by decide
  have hdescent : baseEnd_273184 < baseStart_273184 := by decide
  rcases family_descends (prefixWord ++ tailWord_273184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273241 : List Nat := [1, 2, 1, 2, 2, 5, 6]
def baseStart_273241 : Nat := 118140960795 + 273241 * 2 ^ 59
def prefixEnd_273241 : Nat := 4983230072969 + 3 ^ 40 * 273241 * 2
def baseEnd_273241 : Nat := 27714363953633713981411

theorem tailTrace_273241 : CollatzResearch.WordTrace tailWord_273241 prefixEnd_273241 27714363953633713981411 := by
  unfold tailWord_273241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965918003101997692651577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6643945335401331795101051 9965918003101997692651577)
  ·
    refine ⟨7474438502326498269488683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9965918003101997692651577 7474438502326498269488683)
    ·
      refine ⟨11211657753489747404233025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474438502326498269488683 11211657753489747404233025)
      ·
        refine ⟨8408743315117310553174769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11211657753489747404233025 8408743315117310553174769)
        ·
          refine ⟨6306557486337982914881077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8408743315117310553174769 6306557486337982914881077)
          ·
            refine ⟨591239764344185898270101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6306557486337982914881077 591239764344185898270101)
            ·
              refine ⟨27714363953633713981411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 591239764344185898270101 27714363953633713981411)
              ·
                rfl

theorem cell19_273241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_273241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273241 prefixEnd_273241 := by exact prefixLift 273241
  have htrace : WordTrace (prefixWord ++ tailWord_273241) baseStart_273241 baseEnd_273241 := by
    simpa [prefixWord, tailWord_273241, baseEnd_273241] using wordTrace_append hprefix tailTrace_273241
  have hstable : (prefixWord ++ tailWord_273241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273241).length < 2 ^ (prefixWord ++ tailWord_273241).sum := by decide
  have hdescent : baseEnd_273241 < baseStart_273241 := by decide
  rcases family_descends (prefixWord ++ tailWord_273241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273260 : List Nat := [2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_273260 : Nat := 118140960795 + 273260 * 2 ^ 59
def prefixEnd_273260 : Nat := 4983230072969 + 3 ^ 40 * 273260 * 2
def baseEnd_273260 : Nat := 83148873272714727521959

theorem tailTrace_273260 : CollatzResearch.WordTrace tailWord_273260 prefixEnd_273260 83148873272714727521959 := by
  unfold tailWord_273260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983305495016581968796617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6644407326688775958395489 4983305495016581968796617)
  ·
    refine ⟨3737479121262436476597463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4983305495016581968796617 3737479121262436476597463)
    ·
      refine ⟨5606218681893654714896195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737479121262436476597463 5606218681893654714896195)
      ·
        refine ⟨8409328022840482072344293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5606218681893654714896195 8409328022840482072344293)
        ·
          refine ⟨1576749004282590388564555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8409328022840482072344293 1576749004282590388564555)
          ·
            refine ⟨2365123506423885582846833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576749004282590388564555 2365123506423885582846833)
            ·
              refine ⟨1773842629817914187135125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365123506423885582846833 1773842629817914187135125)
              ·
                refine ⟨83148873272714727521959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1773842629817914187135125 83148873272714727521959)
                ·
                  rfl

theorem cell19_273260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_273260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273260 prefixEnd_273260 := by exact prefixLift 273260
  have htrace : WordTrace (prefixWord ++ tailWord_273260) baseStart_273260 baseEnd_273260 := by
    simpa [prefixWord, tailWord_273260, baseEnd_273260] using wordTrace_append hprefix tailTrace_273260
  have hstable : (prefixWord ++ tailWord_273260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273260).length < 2 ^ (prefixWord ++ tailWord_273260).sum := by decide
  have hdescent : baseEnd_273260 < baseStart_273260 := by decide
  rcases family_descends (prefixWord ++ tailWord_273260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273277 : List Nat := [1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_273277 : Nat := 118140960795 + 273277 * 2 ^ 59
def prefixEnd_273277 : Nat := 4983230072969 + 3 ^ 40 * 273277 * 2
def baseEnd_273277 : Nat := 83154046114863725144135

theorem tailTrace_273277 : CollatzResearch.WordTrace tailWord_273277 prefixEnd_273277 83154046114863725144135 := by
  unfold tailWord_273277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967231030971575840962085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6644820687314383893974723 9967231030971575840962085)
  ·
    refine ⟨1868855818307170470180391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9967231030971575840962085 1868855818307170470180391)
    ·
      refine ⟨2803283727460755705270587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868855818307170470180391 2803283727460755705270587)
      ·
        refine ⟨4204925591191133557905881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803283727460755705270587 4204925591191133557905881)
        ·
          refine ⟨3153694193393350168429411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4204925591191133557905881 3153694193393350168429411)
          ·
            refine ⟨4730541290090025252644117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153694193393350168429411 4730541290090025252644117)
            ·
              refine ⟨221744122972969933717693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4730541290090025252644117 221744122972969933717693)
              ·
                refine ⟨83154046114863725144135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221744122972969933717693 83154046114863725144135)
                ·
                  rfl

theorem cell19_273277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_273277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273277 prefixEnd_273277 := by exact prefixLift 273277
  have htrace : WordTrace (prefixWord ++ tailWord_273277) baseStart_273277 baseEnd_273277 := by
    simpa [prefixWord, tailWord_273277, baseEnd_273277] using wordTrace_append hprefix tailTrace_273277
  have hstable : (prefixWord ++ tailWord_273277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273277).length < 2 ^ (prefixWord ++ tailWord_273277).sum := by decide
  have hdescent : baseEnd_273277 < baseStart_273277 := by decide
  rcases family_descends (prefixWord ++ tailWord_273277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273332 : List Nat := [2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_273332 : Nat := 118140960795 + 273332 * 2 ^ 59
def prefixEnd_273332 : Nat := 4983230072969 + 3 ^ 40 * 273332 * 2
def baseEnd_273332 : Nat := 83170781780639893921763

theorem tailTrace_273332 : CollatzResearch.WordTrace tailWord_273332 prefixEnd_273332 83170781780639893921763 := by
  unfold tailWord_273332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4984618522886160117107125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6646158030514880156142833 4984618522886160117107125)
  ·
    refine ⟨467307986520577510978793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4984618522886160117107125 467307986520577510978793)
    ·
      refine ⟨350480989890433133234095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 467307986520577510978793 350480989890433133234095)
      ·
        refine ⟨525721484835649699851143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350480989890433133234095 525721484835649699851143)
        ·
          refine ⟨788582227253474549776715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525721484835649699851143 788582227253474549776715)
          ·
            refine ⟨1182873340880211824665073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788582227253474549776715 1182873340880211824665073)
            ·
              refine ⟨887155005660158868498805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182873340880211824665073 887155005660158868498805)
              ·
                refine ⟨83170781780639893921763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 887155005660158868498805 83170781780639893921763)
                ·
                  rfl

theorem cell19_273332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_273332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273332 prefixEnd_273332 := by exact prefixLift 273332
  have htrace : WordTrace (prefixWord ++ tailWord_273332) baseStart_273332 baseEnd_273332 := by
    simpa [prefixWord, tailWord_273332, baseEnd_273332] using wordTrace_append hprefix tailTrace_273332
  have hstable : (prefixWord ++ tailWord_273332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273332).length < 2 ^ (prefixWord ++ tailWord_273332).sum := by decide
  have hdescent : baseEnd_273332 < baseStart_273332 := by decide
  rcases family_descends (prefixWord ++ tailWord_273332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273336 : List Nat := [2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_273336 : Nat := 118140960795 + 273336 * 2 ^ 59
def prefixEnd_273336 : Nat := 4983230072969 + 3 ^ 40 * 273336 * 2
def baseEnd_273336 : Nat := 83171998919969069832863

theorem tailTrace_273336 : CollatzResearch.WordTrace tailWord_273336 prefixEnd_273336 83171998919969069832863 := by
  unfold tailWord_273336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4984691468878914458679931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6646255291838552611573241 4984691468878914458679931)
  ·
    refine ⟨7477037203318371688019897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4984691468878914458679931 7477037203318371688019897)
    ·
      refine ⟨5607777902488778766014923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7477037203318371688019897 5607777902488778766014923)
      ·
        refine ⟨8411666853733168149022385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5607777902488778766014923 8411666853733168149022385)
        ·
          refine ⟨6308750140299876111766789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8411666853733168149022385 6308750140299876111766789)
          ·
            refine ⟨1182890651306226770956273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6308750140299876111766789 1182890651306226770956273)
            ·
              refine ⟨887167988479670078217205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182890651306226770956273 887167988479670078217205)
              ·
                refine ⟨83171998919969069832863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 887167988479670078217205 83171998919969069832863)
                ·
                  rfl

theorem cell19_273336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_273336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273336 prefixEnd_273336 := by exact prefixLift 273336
  have htrace : WordTrace (prefixWord ++ tailWord_273336) baseStart_273336 baseEnd_273336 := by
    simpa [prefixWord, tailWord_273336, baseEnd_273336] using wordTrace_append hprefix tailTrace_273336
  have hstable : (prefixWord ++ tailWord_273336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273336).length < 2 ^ (prefixWord ++ tailWord_273336).sum := by decide
  have hdescent : baseEnd_273336 < baseStart_273336 := by decide
  rcases family_descends (prefixWord ++ tailWord_273336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273391 : List Nat := [1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_273391 : Nat := 118140960795 + 273391 * 2 ^ 59
def prefixEnd_273391 : Nat := 4983230072969 + 3 ^ 40 * 273391 * 2
def baseEnd_273391 : Nat := 83188734585745238610491

theorem tailTrace_273391 : CollatzResearch.WordTrace tailWord_273391 prefixEnd_273391 83188734585745238610491 := by
  unfold tailWord_273391
  simp only [CollatzResearch.WordTrace]
  refine ⟨9971388952558573310612027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6647592635039048873741351 9971388952558573310612027)
  ·
    refine ⟨14957083428837859965918041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9971388952558573310612027 14957083428837859965918041)
    ·
      refine ⟨11217812571628394974438531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14957083428837859965918041 11217812571628394974438531)
      ·
        refine ⟨16826718857442592461657797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11217812571628394974438531 16826718857442592461657797)
        ·
          refine ⟨3155009785770486086560837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16826718857442592461657797 3155009785770486086560837)
          ·
            refine ⟨591564334831966141230157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3155009785770486086560837 591564334831966141230157)
            ·
              refine ⟨221836625561987302961309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 591564334831966141230157 221836625561987302961309)
              ·
                refine ⟨83188734585745238610491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221836625561987302961309 83188734585745238610491)
                ·
                  rfl

theorem cell19_273391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_273391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273391 prefixEnd_273391 := by exact prefixLift 273391
  have htrace : WordTrace (prefixWord ++ tailWord_273391) baseStart_273391 baseEnd_273391 := by
    simpa [prefixWord, tailWord_273391, baseEnd_273391] using wordTrace_append hprefix tailTrace_273391
  have hstable : (prefixWord ++ tailWord_273391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273391).length < 2 ^ (prefixWord ++ tailWord_273391).sum := by decide
  have hdescent : baseEnd_273391 < baseStart_273391 := by decide
  rcases family_descends (prefixWord ++ tailWord_273391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273469 : List Nat := [1, 4, 1, 3, 1, 2, 7]
def baseStart_273469 : Nat := 118140960795 + 273469 * 2 ^ 59
def prefixEnd_273469 : Nat := 4983230072969 + 3 ^ 40 * 273469 * 2
def baseEnd_273469 : Nat := 27737489600888056292315

theorem tailTrace_273469 : CollatzResearch.WordTrace tailWord_273469 prefixEnd_273469 27737489600888056292315 := by
  unfold tailWord_273469
  simp only [CollatzResearch.WordTrace]
  refine ⟨9974233846275992631951461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6649489230850661754634307 9974233846275992631951461)
  ·
    refine ⟨1870168846176748618490899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9974233846275992631951461 1870168846176748618490899)
    ·
      refine ⟨2805253269265122927736349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870168846176748618490899 2805253269265122927736349)
      ·
        refine ⟨1051969975974421097901131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2805253269265122927736349 1051969975974421097901131)
        ·
          refine ⟨1577954963961631646851697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051969975974421097901131 1577954963961631646851697)
          ·
            refine ⟨1183466222971223735138773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577954963961631646851697 1183466222971223735138773)
            ·
              refine ⟨27737489600888056292315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1183466222971223735138773 27737489600888056292315)
              ·
                rfl

theorem cell19_273469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_273469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273469 prefixEnd_273469 := by exact prefixLift 273469
  have htrace : WordTrace (prefixWord ++ tailWord_273469) baseStart_273469 baseEnd_273469 := by
    simpa [prefixWord, tailWord_273469, baseEnd_273469] using wordTrace_append hprefix tailTrace_273469
  have hstable : (prefixWord ++ tailWord_273469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273469).length < 2 ^ (prefixWord ++ tailWord_273469).sum := by decide
  have hdescent : baseEnd_273469 < baseStart_273469 := by decide
  rcases family_descends (prefixWord ++ tailWord_273469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273541 : List Nat := [1, 3, 1, 1, 7, 1, 1, 4]
def baseStart_273541 : Nat := 118140960795 + 273541 * 2 ^ 59
def prefixEnd_273541 : Nat := 4983230072969 + 3 ^ 40 * 273541 * 2
def baseEnd_273541 : Nat := 83234377310589335276749

theorem tailTrace_273541 : CollatzResearch.WordTrace tailWord_273541 prefixEnd_273541 83234377310589335276749 := by
  unfold tailWord_273541
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976859902015148928572477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6651239934676765952381651 9976859902015148928572477)
  ·
    refine ⟨3741322463255680848214679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9976859902015148928572477 3741322463255680848214679)
    ·
      refine ⟨5611983694883521272322019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3741322463255680848214679 5611983694883521272322019)
      ·
        refine ⟨8417975542325281908483029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5611983694883521272322019 8417975542325281908483029)
        ·
          refine ⟨197296301773248794730071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8417975542325281908483029 197296301773248794730071)
          ·
            refine ⟨295944452659873192095107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197296301773248794730071 295944452659873192095107)
            ·
              refine ⟨443916678989809788142661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295944452659873192095107 443916678989809788142661)
              ·
                refine ⟨83234377310589335276749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443916678989809788142661 83234377310589335276749)
                ·
                  rfl

theorem cell19_273541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_273541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273541 prefixEnd_273541 := by exact prefixLift 273541
  have htrace : WordTrace (prefixWord ++ tailWord_273541) baseStart_273541 baseEnd_273541 := by
    simpa [prefixWord, tailWord_273541, baseEnd_273541] using wordTrace_append hprefix tailTrace_273541
  have hstable : (prefixWord ++ tailWord_273541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273541).length < 2 ^ (prefixWord ++ tailWord_273541).sum := by decide
  have hdescent : baseEnd_273541 < baseStart_273541 := by decide
  rcases family_descends (prefixWord ++ tailWord_273541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273545 : List Nat := [1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_273545 : Nat := 118140960795 + 273545 * 2 ^ 59
def prefixEnd_273545 : Nat := 4983230072969 + 3 ^ 40 * 273545 * 2
def baseEnd_273545 : Nat := 83235594449918511187849

theorem tailTrace_273545 : CollatzResearch.WordTrace tailWord_273545 prefixEnd_273545 83235594449918511187849 := by
  unfold tailWord_273545
  simp only [CollatzResearch.WordTrace]
  refine ⟨9977005794000657611718089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6651337196000438407812059 9977005794000657611718089)
  ·
    refine ⟨7482754345500493208788567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9977005794000657611718089 7482754345500493208788567)
    ·
      refine ⟨11224131518250739813182851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482754345500493208788567 11224131518250739813182851)
      ·
        refine ⟨16836197277376109719774277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11224131518250739813182851 16836197277376109719774277)
        ·
          refine ⟨3156786989508020572457677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16836197277376109719774277 3156786989508020572457677)
          ·
            refine ⟨1183795121065507714671629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3156786989508020572457677 1183795121065507714671629)
            ·
              refine ⟨443923170399565393001861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1183795121065507714671629 443923170399565393001861)
              ·
                refine ⟨83235594449918511187849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443923170399565393001861 83235594449918511187849)
                ·
                  rfl

theorem cell19_273545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_273545 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273545 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273545 prefixEnd_273545 := by exact prefixLift 273545
  have htrace : WordTrace (prefixWord ++ tailWord_273545) baseStart_273545 baseEnd_273545 := by
    simpa [prefixWord, tailWord_273545, baseEnd_273545] using wordTrace_append hprefix tailTrace_273545
  have hstable : (prefixWord ++ tailWord_273545).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273545).length < 2 ^ (prefixWord ++ tailWord_273545).sum := by decide
  have hdescent : baseEnd_273545 < baseStart_273545 := by decide
  rcases family_descends (prefixWord ++ tailWord_273545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273581 : List Nat := [1, 5, 2, 1, 3, 1, 6]
def baseStart_273581 : Nat := 118140960795 + 273581 * 2 ^ 59
def prefixEnd_273581 : Nat := 4983230072969 + 3 ^ 40 * 273581 * 2
def baseEnd_273581 : Nat := 27748849567960364795917

theorem tailTrace_273581 : CollatzResearch.WordTrace tailWord_273581 prefixEnd_273581 27748849567960364795917 := by
  unfold tailWord_273581
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978318821870235760028597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6652212547913490506685731 9978318821870235760028597)
  ·
    refine ⟨935467389550334602502681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9978318821870235760028597 935467389550334602502681)
    ·
      refine ⟨701600542162750951877011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 935467389550334602502681 701600542162750951877011)
      ·
        refine ⟨1052400813244126427815517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701600542162750951877011 1052400813244126427815517)
        ·
          refine ⟨394650304966547410430819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1052400813244126427815517 394650304966547410430819)
          ·
            refine ⟨591975457449821115646229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394650304966547410430819 591975457449821115646229)
            ·
              refine ⟨27748849567960364795917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 591975457449821115646229 27748849567960364795917)
              ·
                rfl

theorem cell19_273581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_273581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273581 prefixEnd_273581 := by exact prefixLift 273581
  have htrace : WordTrace (prefixWord ++ tailWord_273581) baseStart_273581 baseEnd_273581 := by
    simpa [prefixWord, tailWord_273581, baseEnd_273581] using wordTrace_append hprefix tailTrace_273581
  have hstable : (prefixWord ++ tailWord_273581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273581).length < 2 ^ (prefixWord ++ tailWord_273581).sum := by decide
  have hdescent : baseEnd_273581 < baseStart_273581 := by decide
  rcases family_descends (prefixWord ++ tailWord_273581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273613 : List Nat := [1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_273613 : Nat := 118140960795 + 273613 * 2 ^ 59
def prefixEnd_273613 : Nat := 4983230072969 + 3 ^ 40 * 273613 * 2
def baseEnd_273613 : Nat := 83256285818514501676553

theorem tailTrace_273613 : CollatzResearch.WordTrace tailWord_273613 prefixEnd_273613 83256285818514501676553 := by
  unfold tailWord_273613
  simp only [CollatzResearch.WordTrace]
  refine ⟨9979485957754305225193493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6652990638502870150128995 9979485957754305225193493)
  ·
    refine ⟨467788404269733057430945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9979485957754305225193493 467788404269733057430945)
    ·
      refine ⟨350841303202299793073209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 467788404269733057430945 350841303202299793073209)
      ·
        refine ⟨263130977401724844804907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350841303202299793073209 263130977401724844804907)
        ·
          refine ⟨394696466102587267207361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263130977401724844804907 394696466102587267207361)
          ·
            refine ⟨296022349576940450405521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394696466102587267207361 296022349576940450405521)
            ·
              refine ⟨222016762182705337804141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296022349576940450405521 222016762182705337804141)
              ·
                refine ⟨83256285818514501676553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222016762182705337804141 83256285818514501676553)
                ·
                  rfl

theorem cell19_273613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_273613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273613 prefixEnd_273613 := by exact prefixLift 273613
  have htrace : WordTrace (prefixWord ++ tailWord_273613) baseStart_273613 baseEnd_273613 := by
    simpa [prefixWord, tailWord_273613, baseEnd_273613] using wordTrace_append hprefix tailTrace_273613
  have hstable : (prefixWord ++ tailWord_273613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273613).length < 2 ^ (prefixWord ++ tailWord_273613).sum := by decide
  have hdescent : baseEnd_273613 < baseStart_273613 := by decide
  rcases family_descends (prefixWord ++ tailWord_273613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273678 : List Nat := [4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_273678 : Nat := 118140960795 + 273678 * 2 ^ 59
def prefixEnd_273678 : Nat := 4983230072969 + 3 ^ 40 * 273678 * 2
def baseEnd_273678 : Nat := 83276064332613610231931

theorem tailTrace_273678 : CollatzResearch.WordTrace tailWord_273678 prefixEnd_273678 83276064332613610231931 := by
  unfold tailWord_273678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247732087814852665788711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6654571135012547550873125 1247732087814852665788711)
  ·
    refine ⟨1871598131722278998683067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1247732087814852665788711 1871598131722278998683067)
    ·
      refine ⟨2807397197583418498024601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871598131722278998683067 2807397197583418498024601)
      ·
        refine ⟨2105547898187563873518451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2807397197583418498024601 2105547898187563873518451)
        ·
          refine ⟨3158321847281345810277677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105547898187563873518451 3158321847281345810277677)
          ·
            refine ⟨1184370692730504678854129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3158321847281345810277677 1184370692730504678854129)
            ·
              refine ⟨888278019547878509140597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184370692730504678854129 888278019547878509140597)
              ·
                refine ⟨83276064332613610231931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 888278019547878509140597 83276064332613610231931)
                ·
                  rfl

theorem cell19_273678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_273678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273678 prefixEnd_273678 := by exact prefixLift 273678
  have htrace : WordTrace (prefixWord ++ tailWord_273678) baseStart_273678 baseEnd_273678 := by
    simpa [prefixWord, tailWord_273678, baseEnd_273678] using wordTrace_append hprefix tailTrace_273678
  have hstable : (prefixWord ++ tailWord_273678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273678).length < 2 ^ (prefixWord ++ tailWord_273678).sum := by decide
  have hdescent : baseEnd_273678 < baseStart_273678 := by decide
  rcases family_descends (prefixWord ++ tailWord_273678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273699 : List Nat := [1, 1, 1, 4, 2, 10]
def baseStart_273699 : Nat := 118140960795 + 273699 * 2 ^ 59
def prefixEnd_273699 : Nat := 4983230072969 + 3 ^ 40 * 273699 * 2
def baseEnd_273699 : Nat := 9253606034899087085023

theorem tailTrace_273699 : CollatzResearch.WordTrace tailWord_273699 prefixEnd_273699 9253606034899087085023 := by
  unfold tailWord_273699
  simp only [CollatzResearch.WordTrace]
  refine ⟨9982622635442741912824151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6655081756961827941882767 9982622635442741912824151)
  ·
    refine ⟨14973933953164112869236227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9982622635442741912824151 14973933953164112869236227)
    ·
      refine ⟨22460900929746169303854341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14973933953164112869236227 22460900929746169303854341)
      ·
        refine ⟨4211418924327406744472689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22460900929746169303854341 4211418924327406744472689)
        ·
          refine ⟨3158564193245555058354517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4211418924327406744472689 3158564193245555058354517)
          ·
            refine ⟨9253606034899087085023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3158564193245555058354517 9253606034899087085023)
            ·
              rfl

theorem cell19_273699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_273699 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273699 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273699 prefixEnd_273699 := by exact prefixLift 273699
  have htrace : WordTrace (prefixWord ++ tailWord_273699) baseStart_273699 baseEnd_273699 := by
    simpa [prefixWord, tailWord_273699, baseEnd_273699] using wordTrace_append hprefix tailTrace_273699
  have hstable : (prefixWord ++ tailWord_273699).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273699).length < 2 ^ (prefixWord ++ tailWord_273699).sum := by decide
  have hdescent : baseEnd_273699 < baseStart_273699 := by decide
  rcases family_descends (prefixWord ++ tailWord_273699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273714 : List Nat := [3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_273714 : Nat := 118140960795 + 273714 * 2 ^ 59
def prefixEnd_273714 : Nat := 4983230072969 + 3 ^ 40 * 273714 * 2
def baseEnd_273714 : Nat := 83287018586576193431833

theorem tailTrace_273714 : CollatzResearch.WordTrace tailWord_273714 prefixEnd_273714 83287018586576193431833 := by
  unfold tailWord_273714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495792432597099868655049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6655446486925599649746797 2495792432597099868655049)
  ·
    refine ⟨1871844324447824901491287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2495792432597099868655049 1871844324447824901491287)
    ·
      refine ⟨2807766486671737352236931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871844324447824901491287 2807766486671737352236931)
      ·
        refine ⟨4211649730007606028355397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807766486671737352236931 4211649730007606028355397)
        ·
          refine ⟨789684324376426130316637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4211649730007606028355397 789684324376426130316637)
          ·
            refine ⟨296131621641159798868739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 789684324376426130316637 296131621641159798868739)
            ·
              refine ⟨444197432461739698303109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296131621641159798868739 444197432461739698303109)
              ·
                refine ⟨83287018586576193431833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 444197432461739698303109 83287018586576193431833)
                ·
                  rfl

theorem cell19_273714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_273714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273714 prefixEnd_273714 := by exact prefixLift 273714
  have htrace : WordTrace (prefixWord ++ tailWord_273714) baseStart_273714 baseEnd_273714 := by
    simpa [prefixWord, tailWord_273714, baseEnd_273714] using wordTrace_append hprefix tailTrace_273714
  have hstable : (prefixWord ++ tailWord_273714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273714).length < 2 ^ (prefixWord ++ tailWord_273714).sum := by decide
  have hdescent : baseEnd_273714 < baseStart_273714 := by decide
  rcases family_descends (prefixWord ++ tailWord_273714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273737 : List Nat := [1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_273737 : Nat := 118140960795 + 273737 * 2 ^ 59
def prefixEnd_273737 : Nat := 4983230072969 + 3 ^ 40 * 273737 * 2
def baseEnd_273737 : Nat := 83294017137718954920659

theorem tailTrace_273737 : CollatzResearch.WordTrace tailWord_273737 prefixEnd_273737 83294017137718954920659 := by
  unfold tailWord_273737
  simp only [CollatzResearch.WordTrace]
  refine ⟨9984008609305074402707465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6656005739536716268471643 9984008609305074402707465)
  ·
    refine ⟨7488006456978805802030599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9984008609305074402707465 7488006456978805802030599)
    ·
      refine ⟨11232009685468208703045899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7488006456978805802030599 11232009685468208703045899)
      ·
        refine ⟨16848014528202313054568849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11232009685468208703045899 16848014528202313054568849)
        ·
          refine ⟨12636010896151734790926637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16848014528202313054568849 12636010896151734790926637)
          ·
            refine ⟨4738504086056900546597489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12636010896151734790926637 4738504086056900546597489)
            ·
              refine ⟨3553878064542675409948117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738504086056900546597489 3553878064542675409948117)
              ·
                refine ⟨83294017137718954920659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3553878064542675409948117 83294017137718954920659)
                ·
                  rfl

theorem cell19_273737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_273737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273737 prefixEnd_273737 := by exact prefixLift 273737
  have htrace : WordTrace (prefixWord ++ tailWord_273737) baseStart_273737 baseEnd_273737 := by
    simpa [prefixWord, tailWord_273737, baseEnd_273737] using wordTrace_append hprefix tailTrace_273737
  have hstable : (prefixWord ++ tailWord_273737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273737).length < 2 ^ (prefixWord ++ tailWord_273737).sum := by decide
  have hdescent : baseEnd_273737 < baseStart_273737 := by decide
  rcases family_descends (prefixWord ++ tailWord_273737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273775 : List Nat := [1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_273775 : Nat := 118140960795 + 273775 * 2 ^ 59
def prefixEnd_273775 : Nat := 4983230072969 + 3 ^ 40 * 273775 * 2
def baseEnd_273775 : Nat := 83305579961346126076111

theorem tailTrace_273775 : CollatzResearch.WordTrace tailWord_273775 prefixEnd_273775 83305579961346126076111 := by
  unfold tailWord_273775
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985394583167406892590779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6656929722111604595060519 9985394583167406892590779)
  ·
    refine ⟨14978091874751110338886169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9985394583167406892590779 14978091874751110338886169)
    ·
      refine ⟨11233568906063332754164627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14978091874751110338886169 11233568906063332754164627)
      ·
        refine ⟨16850353359094999131246941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11233568906063332754164627 16850353359094999131246941)
        ·
          refine ⟨6318882509660624674217603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16850353359094999131246941 6318882509660624674217603)
          ·
            refine ⟨9478323764490937011326405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6318882509660624674217603 9478323764490937011326405)
            ·
              refine ⟨1777185705842050689623701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9478323764490937011326405 1777185705842050689623701)
              ·
                refine ⟨83305579961346126076111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1777185705842050689623701 83305579961346126076111)
                ·
                  rfl

theorem cell19_273775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_273775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273775 prefixEnd_273775 := by exact prefixLift 273775
  have htrace : WordTrace (prefixWord ++ tailWord_273775) baseStart_273775 baseEnd_273775 := by
    simpa [prefixWord, tailWord_273775, baseEnd_273775] using wordTrace_append hprefix tailTrace_273775
  have hstable : (prefixWord ++ tailWord_273775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273775).length < 2 ^ (prefixWord ++ tailWord_273775).sum := by decide
  have hdescent : baseEnd_273775 < baseStart_273775 := by decide
  rcases family_descends (prefixWord ++ tailWord_273775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273813 : List Nat := [1, 3, 2, 1, 1, 2, 9]
def baseStart_273813 : Nat := 118140960795 + 273813 * 2 ^ 59
def prefixEnd_273813 : Nat := 4983230072969 + 3 ^ 40 * 273813 * 2
def baseEnd_273813 : Nat := 27772380928324432410521

theorem tailTrace_273813 : CollatzResearch.WordTrace tailWord_273813 prefixEnd_273813 27772380928324432410521 := by
  unfold tailWord_273813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986780557029739382474093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6657853704686492921649395 9986780557029739382474093)
  ·
    refine ⟨3745042708886152268427785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9986780557029739382474093 3745042708886152268427785)
    ·
      refine ⟨2808782031664614201320839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3745042708886152268427785 2808782031664614201320839)
      ·
        refine ⟨4213173047496921301981259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808782031664614201320839 4213173047496921301981259)
        ·
          refine ⟨6319759571245381952971889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4213173047496921301981259 6319759571245381952971889)
          ·
            refine ⟨4739819678434036464728917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6319759571245381952971889 4739819678434036464728917)
            ·
              refine ⟨27772380928324432410521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4739819678434036464728917 27772380928324432410521)
              ·
                rfl

theorem cell19_273813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_273813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273813 prefixEnd_273813 := by exact prefixLift 273813
  have htrace : WordTrace (prefixWord ++ tailWord_273813) baseStart_273813 baseEnd_273813 := by
    simpa [prefixWord, tailWord_273813, baseEnd_273813] using wordTrace_append hprefix tailTrace_273813
  have hstable : (prefixWord ++ tailWord_273813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273813).length < 2 ^ (prefixWord ++ tailWord_273813).sum := by decide
  have hdescent : baseEnd_273813 < baseStart_273813 := by decide
  rcases family_descends (prefixWord ++ tailWord_273813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273885 : List Nat := [1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_273885 : Nat := 118140960795 + 273885 * 2 ^ 59
def prefixEnd_273885 : Nat := 4983230072969 + 3 ^ 40 * 273885 * 2
def baseEnd_273885 : Nat := 83339051292898463631367

theorem tailTrace_273885 : CollatzResearch.WordTrace tailWord_273885 prefixEnd_273885 83339051292898463631367 := by
  unfold tailWord_273885
  simp only [CollatzResearch.WordTrace]
  refine ⟨9989406612768895679095109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6659604408512597119396739 9989406612768895679095109)
  ·
    refine ⟨1873013739894167939830333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9989406612768895679095109 1873013739894167939830333)
    ·
      refine ⟨702380152460312977436375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1873013739894167939830333 702380152460312977436375)
      ·
        refine ⟨1053570228690469466154563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702380152460312977436375 1053570228690469466154563)
        ·
          refine ⟨1580355343035704199231845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053570228690469466154563 1580355343035704199231845)
          ·
            refine ⟨296316626819194537355971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1580355343035704199231845 296316626819194537355971)
            ·
              refine ⟨444474940228791806033957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296316626819194537355971 444474940228791806033957)
              ·
                refine ⟨83339051292898463631367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 444474940228791806033957 83339051292898463631367)
                ·
                  rfl

theorem cell19_273885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_273885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273885 prefixEnd_273885 := by exact prefixLift 273885
  have htrace : WordTrace (prefixWord ++ tailWord_273885) baseStart_273885 baseEnd_273885 := by
    simpa [prefixWord, tailWord_273885, baseEnd_273885] using wordTrace_append hprefix tailTrace_273885
  have hstable : (prefixWord ++ tailWord_273885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273885).length < 2 ^ (prefixWord ++ tailWord_273885).sum := by decide
  have hdescent : baseEnd_273885 < baseStart_273885 := by decide
  rcases family_descends (prefixWord ++ tailWord_273885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273946 : List Nat := [3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_273946 : Nat := 118140960795 + 273946 * 2 ^ 59
def prefixEnd_273946 : Nat := 4983230072969 + 3 ^ 40 * 273946 * 2
def baseEnd_273946 : Nat := 83357612667668396275645

theorem tailTrace_273946 : CollatzResearch.WordTrace tailWord_273946 prefixEnd_273946 83357612667668396275645 := by
  unfold tailWord_273946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2497907866386975774266423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6661087643698602064710461 2497907866386975774266423)
  ·
    refine ⟨3746861799580463661399635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2497907866386975774266423 3746861799580463661399635)
    ·
      refine ⟨5620292699370695492099453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3746861799580463661399635 5620292699370695492099453)
      ·
        refine ⟨2107609762264010809537295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5620292699370695492099453 2107609762264010809537295)
        ·
          refine ⟨3161414643396016214305943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107609762264010809537295 3161414643396016214305943)
          ·
            refine ⟨4742121965094024321458915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161414643396016214305943 4742121965094024321458915)
            ·
              refine ⟨7113182947641036482188373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742121965094024321458915 7113182947641036482188373)
              ·
                refine ⟨83357612667668396275645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7113182947641036482188373 83357612667668396275645)
                ·
                  rfl

theorem cell19_273946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_273946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273946 prefixEnd_273946 := by exact prefixLift 273946
  have htrace : WordTrace (prefixWord ++ tailWord_273946) baseStart_273946 baseEnd_273946 := by
    simpa [prefixWord, tailWord_273946, baseEnd_273946] using wordTrace_append hprefix tailTrace_273946
  have hstable : (prefixWord ++ tailWord_273946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273946).length < 2 ^ (prefixWord ++ tailWord_273946).sum := by decide
  have hdescent : baseEnd_273946 < baseStart_273946 := by decide
  rcases family_descends (prefixWord ++ tailWord_273946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273980 : List Nat := [2, 2, 2, 2, 5, 1, 5]
def baseStart_273980 : Nat := 118140960795 + 273980 * 2 ^ 59
def prefixEnd_273980 : Nat := 4983230072969 + 3 ^ 40 * 273980 * 2
def baseEnd_273980 : Nat := 27789319450655463839999

theorem tailTrace_273980 : CollatzResearch.WordTrace tailWord_273980 prefixEnd_273980 27789319450655463839999 := by
  unfold tailWord_273980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4996435773712363451901697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6661914364949817935868929 4996435773712363451901697)
  ·
    refine ⟨3747326830284272588926273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4996435773712363451901697 3747326830284272588926273)
    ·
      refine ⟨2810495122713204441694705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3747326830284272588926273 2810495122713204441694705)
      ·
        refine ⟨2107871342034903331271029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2810495122713204441694705 2107871342034903331271029)
        ·
          refine ⟨197612938315772187306659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2107871342034903331271029 197612938315772187306659)
          ·
            refine ⟨296419407473658280959989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197612938315772187306659 296419407473658280959989)
            ·
              refine ⟨27789319450655463839999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296419407473658280959989 27789319450655463839999)
              ·
                rfl

theorem cell19_273980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_273980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_273980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_273980 prefixEnd_273980 := by exact prefixLift 273980
  have htrace : WordTrace (prefixWord ++ tailWord_273980) baseStart_273980 baseEnd_273980 := by
    simpa [prefixWord, tailWord_273980, baseEnd_273980] using wordTrace_append hprefix tailTrace_273980
  have hstable : (prefixWord ++ tailWord_273980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273980).length < 2 ^ (prefixWord ++ tailWord_273980).sum := by decide
  have hdescent : baseEnd_273980 < baseStart_273980 := by decide
  rcases family_descends (prefixWord ++ tailWord_273980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274058 : List Nat := [3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_274058 : Nat := 118140960795 + 274058 * 2 ^ 59
def prefixEnd_274058 : Nat := 4983230072969 + 3 ^ 40 * 274058 * 2
def baseEnd_274058 : Nat := 83391692568885321786451

theorem tailTrace_274058 : CollatzResearch.WordTrace tailWord_274058 prefixEnd_274058 83391692568885321786451 := by
  unfold tailWord_274058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498929110285536556285707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6663810960761430816761885 2498929110285536556285707)
  ·
    refine ⟨3748393665428304834428561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2498929110285536556285707 3748393665428304834428561)
    ·
      refine ⟨2811295249071228625821421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3748393665428304834428561 2811295249071228625821421)
      ·
        refine ⟨1054235718401710734683033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2811295249071228625821421 1054235718401710734683033)
        ·
          refine ⟨790676788801283051012275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054235718401710734683033 790676788801283051012275)
          ·
            refine ⟨1186015183201924576518413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790676788801283051012275 1186015183201924576518413)
            ·
              refine ⟨444755693700721716194405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1186015183201924576518413 444755693700721716194405)
              ·
                refine ⟨83391692568885321786451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 444755693700721716194405 83391692568885321786451)
                ·
                  rfl

theorem cell19_274058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_274058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274058 prefixEnd_274058 := by exact prefixLift 274058
  have htrace : WordTrace (prefixWord ++ tailWord_274058) baseStart_274058 baseEnd_274058 := by
    simpa [prefixWord, tailWord_274058, baseEnd_274058] using wordTrace_append hprefix tailTrace_274058
  have hstable : (prefixWord ++ tailWord_274058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274058).length < 2 ^ (prefixWord ++ tailWord_274058).sum := by decide
  have hdescent : baseEnd_274058 < baseStart_274058 := by decide
  rcases family_descends (prefixWord ++ tailWord_274058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274094 : List Nat := [4, 1, 4, 1, 2, 1, 6]
def baseStart_274094 : Nat := 118140960795 + 274094 * 2 ^ 59
def prefixEnd_274094 : Nat := 4983230072969 + 3 ^ 40 * 274094 * 2
def baseEnd_274094 : Nat := 27800882274282634995451

theorem tailTrace_274094 : CollatzResearch.WordTrace tailWord_274094 prefixEnd_274094 27800882274282634995451 := by
  unfold tailWord_274094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249628683626465546681667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6664686312674482915635557 1249628683626465546681667)
  ·
    refine ⟨1874443025439698320022501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1249628683626465546681667 1874443025439698320022501)
    ·
      refine ⟨351458067269943435004219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1874443025439698320022501 351458067269943435004219)
      ·
        refine ⟨527187100904915152506329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351458067269943435004219 527187100904915152506329)
        ·
          refine ⟨395390325678686364379747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527187100904915152506329 395390325678686364379747)
          ·
            refine ⟨593085488518029546569621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395390325678686364379747 593085488518029546569621)
            ·
              refine ⟨27800882274282634995451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 593085488518029546569621 27800882274282634995451)
              ·
                rfl

theorem cell19_274094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_274094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274094 prefixEnd_274094 := by exact prefixLift 274094
  have htrace : WordTrace (prefixWord ++ tailWord_274094) baseStart_274094 baseEnd_274094 := by
    simpa [prefixWord, tailWord_274094, baseEnd_274094] using wordTrace_append hprefix tailTrace_274094
  have hstable : (prefixWord ++ tailWord_274094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274094).length < 2 ^ (prefixWord ++ tailWord_274094).sum := by decide
  have hdescent : baseEnd_274094 < baseStart_274094 := by decide
  rcases family_descends (prefixWord ++ tailWord_274094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274132 : List Nat := [2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_274132 : Nat := 118140960795 + 274132 * 2 ^ 59
def prefixEnd_274132 : Nat := 4983230072969 + 3 ^ 40 * 274132 * 2
def baseEnd_274132 : Nat := 83414209646475076141805

theorem tailTrace_274132 : CollatzResearch.WordTrace tailWord_274132 prefixEnd_274132 83414209646475076141805 := by
  unfold tailWord_274132
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999207721437028431668325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6665610295249371242224433 4999207721437028431668325)
  ·
    refine ⟨937351447769442830937811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4999207721437028431668325 937351447769442830937811)
    ·
      refine ⟨1406027171654164246406717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937351447769442830937811 1406027171654164246406717)
      ·
        refine ⟨527260189370311592402519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1406027171654164246406717 527260189370311592402519)
        ·
          refine ⟨790890284055467388603779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527260189370311592402519 790890284055467388603779)
          ·
            refine ⟨1186335426083201082905669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790890284055467388603779 1186335426083201082905669)
            ·
              refine ⟨222437892390600203044813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1186335426083201082905669 222437892390600203044813)
              ·
                refine ⟨83414209646475076141805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222437892390600203044813 83414209646475076141805)
                ·
                  rfl

theorem cell19_274132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_274132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274132 prefixEnd_274132 := by exact prefixLift 274132
  have htrace : WordTrace (prefixWord ++ tailWord_274132) baseStart_274132 baseEnd_274132 := by
    simpa [prefixWord, tailWord_274132, baseEnd_274132] using wordTrace_append hprefix tailTrace_274132
  have hstable : (prefixWord ++ tailWord_274132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274132).length < 2 ^ (prefixWord ++ tailWord_274132).sum := by decide
  have hdescent : baseEnd_274132 < baseStart_274132 := by decide
  rcases family_descends (prefixWord ++ tailWord_274132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274136 : List Nat := [2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_274136 : Nat := 118140960795 + 274136 * 2 ^ 59
def prefixEnd_274136 : Nat := 4983230072969 + 3 ^ 40 * 274136 * 2
def baseEnd_274136 : Nat := 83415426785804252052905

theorem tailTrace_274136 : CollatzResearch.WordTrace tailWord_274136 prefixEnd_274136 83415426785804252052905 := by
  unfold tailWord_274136
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999280667429782773241131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6665707556573043697654841 4999280667429782773241131)
  ·
    refine ⟨7498921001144674159861697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4999280667429782773241131 7498921001144674159861697)
    ·
      refine ⟨5624190750858505619896273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7498921001144674159861697 5624190750858505619896273)
      ·
        refine ⟨4218143063143879214922205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5624190750858505619896273 4218143063143879214922205)
        ·
          refine ⟨1581803648678954705595827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4218143063143879214922205 1581803648678954705595827)
          ·
            refine ⟨2372705473018432058393741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581803648678954705595827 2372705473018432058393741)
            ·
              refine ⟨889764552381912021897653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2372705473018432058393741 889764552381912021897653)
              ·
                refine ⟨83415426785804252052905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 889764552381912021897653 83415426785804252052905)
                ·
                  rfl

theorem cell19_274136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_274136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274136 prefixEnd_274136 := by exact prefixLift 274136
  have htrace : WordTrace (prefixWord ++ tailWord_274136) baseStart_274136 baseEnd_274136 := by
    simpa [prefixWord, tailWord_274136, baseEnd_274136] using wordTrace_append hprefix tailTrace_274136
  have hstable : (prefixWord ++ tailWord_274136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274136).length < 2 ^ (prefixWord ++ tailWord_274136).sum := by decide
  have hdescent : baseEnd_274136 < baseStart_274136 := by decide
  rcases family_descends (prefixWord ++ tailWord_274136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274151 : List Nat := [1, 1, 5, 4, 1, 2, 5]
def baseStart_274151 : Nat := 118140960795 + 274151 * 2 ^ 59
def prefixEnd_274151 : Nat := 4983230072969 + 3 ^ 40 * 274151 * 2
def baseEnd_274151 : Nat := 27806663686096220573177

theorem tailTrace_274151 : CollatzResearch.WordTrace tailWord_274151 prefixEnd_274151 27806663686096220573177 := by
  unfold tailWord_274151
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999108429805223108278307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6666072286536815405518871 9999108429805223108278307)
  ·
    refine ⟨14998662644707834662417461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9999108429805223108278307 14998662644707834662417461)
    ·
      refine ⟨1406124622941359499601637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14998662644707834662417461 1406124622941359499601637)
      ·
        refine ⟨263648366801504906175307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1406124622941359499601637 263648366801504906175307)
        ·
          refine ⟨395472550202257359262961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263648366801504906175307 395472550202257359262961)
          ·
            refine ⟨296604412651693019447221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395472550202257359262961 296604412651693019447221)
            ·
              refine ⟨27806663686096220573177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296604412651693019447221 27806663686096220573177)
              ·
                rfl

theorem cell19_274151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_274151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274151 prefixEnd_274151 := by exact prefixLift 274151
  have htrace : WordTrace (prefixWord ++ tailWord_274151) baseStart_274151 baseEnd_274151 := by
    simpa [prefixWord, tailWord_274151, baseEnd_274151] using wordTrace_append hprefix tailTrace_274151
  have hstable : (prefixWord ++ tailWord_274151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274151).length < 2 ^ (prefixWord ++ tailWord_274151).sum := by decide
  have hdescent : baseEnd_274151 < baseStart_274151 := by decide
  rcases family_descends (prefixWord ++ tailWord_274151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274206 : List Nat := [4, 3, 2, 2, 2, 6]
def baseStart_274206 : Nat := 118140960795 + 274206 * 2 ^ 59
def prefixEnd_274206 : Nat := 4983230072969 + 3 ^ 40 * 274206 * 2
def baseEnd_274206 : Nat := 9270747413784981166351

theorem tailTrace_274206 : CollatzResearch.WordTrace tailWord_274206 prefixEnd_274206 9270747413784981166351 := by
  unfold tailWord_274206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250139305575745937691309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6667409629737311667686981 1250139305575745937691309)
  ·
    refine ⟨468802239590904726634241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1250139305575745937691309 468802239590904726634241)
    ·
      refine ⟨351601679693178544975681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 468802239590904726634241 351601679693178544975681)
      ·
        refine ⟨263701259769883908731761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351601679693178544975681 263701259769883908731761)
        ·
          refine ⟨197775944827412931548821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263701259769883908731761 197775944827412931548821)
          ·
            refine ⟨9270747413784981166351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 197775944827412931548821 9270747413784981166351)
            ·
              rfl

theorem cell19_274206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_274206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274206 prefixEnd_274206 := by exact prefixLift 274206
  have htrace : WordTrace (prefixWord ++ tailWord_274206) baseStart_274206 baseEnd_274206 := by
    simpa [prefixWord, tailWord_274206, baseEnd_274206] using wordTrace_append hprefix tailTrace_274206
  have hstable : (prefixWord ++ tailWord_274206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274206).length < 2 ^ (prefixWord ++ tailWord_274206).sum := by decide
  have hdescent : baseEnd_274206 < baseStart_274206 := by decide
  rcases family_descends (prefixWord ++ tailWord_274206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274212 : List Nat := [2, 3, 1, 3, 2, 8]
def baseStart_274212 : Nat := 118140960795 + 274212 * 2 ^ 59
def prefixEnd_274212 : Nat := 4983230072969 + 3 ^ 40 * 274212 * 2
def baseEnd_274212 : Nat := 9270950270339843818201

theorem tailTrace_274212 : CollatzResearch.WordTrace tailWord_274212 prefixEnd_274212 9270950270339843818201 := by
  unfold tailWord_274212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000666641292115263124445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6667555521722820350832593 5000666641292115263124445)
  ·
    refine ⟨1875249990484543223671667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5000666641292115263124445 1875249990484543223671667)
    ·
      refine ⟨2812874985726814835507501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875249990484543223671667 2812874985726814835507501)
      ·
        refine ⟨1054828119647555563315313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2812874985726814835507501 1054828119647555563315313)
        ·
          refine ⟨791121089735666672486485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054828119647555563315313 791121089735666672486485)
          ·
            refine ⟨9270950270339843818201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 791121089735666672486485 9270950270339843818201)
            ·
              rfl

theorem cell19_274212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_274212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274212 prefixEnd_274212 := by exact prefixLift 274212
  have htrace : WordTrace (prefixWord ++ tailWord_274212) baseStart_274212 baseEnd_274212 := by
    simpa [prefixWord, tailWord_274212, baseEnd_274212] using wordTrace_append hprefix tailTrace_274212
  have hstable : (prefixWord ++ tailWord_274212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274212).length < 2 ^ (prefixWord ++ tailWord_274212).sum := by decide
  have hdescent : baseEnd_274212 < baseStart_274212 := by decide
  rcases family_descends (prefixWord ++ tailWord_274212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274227 : List Nat := [1, 1, 1, 2, 8, 1, 1, 4]
def baseStart_274227 : Nat := 118140960795 + 274227 * 2 ^ 59
def prefixEnd_274227 : Nat := 4983230072969 + 3 ^ 40 * 274227 * 2
def baseEnd_274227 : Nat := 83443116705543004030435

theorem tailTrace_274227 : CollatzResearch.WordTrace tailWord_274227 prefixEnd_274227 83443116705543004030435 := by
  unfold tailWord_274227
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001880377529888088044935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6667920251686592058696623 10001880377529888088044935)
  ·
    refine ⟨15002820566294832132067403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10001880377529888088044935 15002820566294832132067403)
    ·
      refine ⟨22504230849442248198101105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15002820566294832132067403 22504230849442248198101105)
      ·
        refine ⟨16878173137081686148575829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22504230849442248198101105 16878173137081686148575829)
        ·
          refine ⟨197791091450176009553623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 16878173137081686148575829 197791091450176009553623)
          ·
            refine ⟨296686637175264014330435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197791091450176009553623 296686637175264014330435)
            ·
              refine ⟨445029955762896021495653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296686637175264014330435 445029955762896021495653)
              ·
                refine ⟨83443116705543004030435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445029955762896021495653 83443116705543004030435)
                ·
                  rfl

theorem cell19_274227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_274227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274227 prefixEnd_274227 := by exact prefixLift 274227
  have htrace : WordTrace (prefixWord ++ tailWord_274227) baseStart_274227 baseEnd_274227 := by
    simpa [prefixWord, tailWord_274227, baseEnd_274227] using wordTrace_append hprefix tailTrace_274227
  have hstable : (prefixWord ++ tailWord_274227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274227).length < 2 ^ (prefixWord ++ tailWord_274227).sum := by decide
  have hdescent : baseEnd_274227 < baseStart_274227 := by decide
  rcases family_descends (prefixWord ++ tailWord_274227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274248 : List Nat := [2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_274248 : Nat := 118140960795 + 274248 * 2 ^ 59
def prefixEnd_274248 : Nat := 4983230072969 + 3 ^ 40 * 274248 * 2
def baseEnd_274248 : Nat := 83449506687021177563711

theorem tailTrace_274248 : CollatzResearch.WordTrace tailWord_274248 prefixEnd_274248 83449506687021177563711 := by
  unfold tailWord_274248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5001323155226904337279699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6668430873635872449706265 5001323155226904337279699)
  ·
    refine ⟨7501984732840356505919549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5001323155226904337279699 7501984732840356505919549)
    ·
      refine ⟨2813244274815133689719831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7501984732840356505919549 2813244274815133689719831)
      ·
        refine ⟨4219866412222700534579747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2813244274815133689719831 4219866412222700534579747)
        ·
          refine ⟨6329799618334050801869621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219866412222700534579747 6329799618334050801869621)
          ·
            refine ⟨593418714218817262675277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6329799618334050801869621 593418714218817262675277)
            ·
              refine ⟨222532017832056473503229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 593418714218817262675277 222532017832056473503229)
              ·
                refine ⟨83449506687021177563711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222532017832056473503229 83449506687021177563711)
                ·
                  rfl

theorem cell19_274248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_274248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274248 prefixEnd_274248 := by exact prefixLift 274248
  have htrace : WordTrace (prefixWord ++ tailWord_274248) baseStart_274248 baseEnd_274248 := by
    simpa [prefixWord, tailWord_274248, baseEnd_274248] using wordTrace_append hprefix tailTrace_274248
  have hstable : (prefixWord ++ tailWord_274248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274248).length < 2 ^ (prefixWord ++ tailWord_274248).sum := by decide
  have hdescent : baseEnd_274248 < baseStart_274248 := by decide
  rcases family_descends (prefixWord ++ tailWord_274248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274307 : List Nat := [1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_274307 : Nat := 118140960795 + 274307 * 2 ^ 59
def prefixEnd_274307 : Nat := 4983230072969 + 3 ^ 40 * 274307 * 2
def baseEnd_274307 : Nat := 83467459492126522252439

theorem tailTrace_274307 : CollatzResearch.WordTrace tailWord_274307 prefixEnd_274307 83467459492126522252439 := by
  unfold tailWord_274307
  simp only [CollatzResearch.WordTrace]
  refine ⟨10004798217240061750957175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6669865478160041167304783 10004798217240061750957175)
  ·
    refine ⟨15007197325860092626435763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10004798217240061750957175 15007197325860092626435763)
    ·
      refine ⟨22510795988790138939653645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15007197325860092626435763 22510795988790138939653645)
      ·
        refine ⟨8441548495796302102370117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22510795988790138939653645 8441548495796302102370117)
        ·
          refine ⟨1582790342961806644194397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8441548495796302102370117 1582790342961806644194397)
          ·
            refine ⟨593546378610677491572899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1582790342961806644194397 593546378610677491572899)
            ·
              refine ⟨890319567916016237359349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593546378610677491572899 890319567916016237359349)
              ·
                refine ⟨83467459492126522252439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 890319567916016237359349 83467459492126522252439)
                ·
                  rfl

theorem cell19_274307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_274307 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274307 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274307 prefixEnd_274307 := by exact prefixLift 274307
  have htrace : WordTrace (prefixWord ++ tailWord_274307) baseStart_274307 baseEnd_274307 := by
    simpa [prefixWord, tailWord_274307, baseEnd_274307] using wordTrace_append hprefix tailTrace_274307
  have hstable : (prefixWord ++ tailWord_274307).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274307).length < 2 ^ (prefixWord ++ tailWord_274307).sum := by decide
  have hdescent : baseEnd_274307 < baseStart_274307 := by decide
  rcases family_descends (prefixWord ++ tailWord_274307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274324 : List Nat := [2, 4, 2, 1, 1, 4, 5]
def baseStart_274324 : Nat := 118140960795 + 274324 * 2 ^ 59
def prefixEnd_274324 : Nat := 4983230072969 + 3 ^ 40 * 274324 * 2
def baseEnd_274324 : Nat := 27824210778091839958205

theorem tailTrace_274324 : CollatzResearch.WordTrace tailWord_274324 prefixEnd_274324 27824210778091839958205 := by
  unfold tailWord_274324
  simp only [CollatzResearch.WordTrace]
  refine ⟨5002709129089236827163013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6670278838785649102884017 5002709129089236827163013)
  ·
    refine ⟨938007961704231905093065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5002709129089236827163013 938007961704231905093065)
    ·
      refine ⟨703505971278173928819799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 938007961704231905093065 703505971278173928819799)
      ·
        refine ⟨1055258956917260893229699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703505971278173928819799 1055258956917260893229699)
        ·
          refine ⟨1582888435375891339844549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055258956917260893229699 1582888435375891339844549)
          ·
            refine ⟨296791581632979626220853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1582888435375891339844549 296791581632979626220853)
            ·
              refine ⟨27824210778091839958205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296791581632979626220853 27824210778091839958205)
              ·
                rfl

theorem cell19_274324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_274324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274324 prefixEnd_274324 := by exact prefixLift 274324
  have htrace : WordTrace (prefixWord ++ tailWord_274324) baseStart_274324 baseEnd_274324 := by
    simpa [prefixWord, tailWord_274324, baseEnd_274324] using wordTrace_append hprefix tailTrace_274324
  have hstable : (prefixWord ++ tailWord_274324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274324).length < 2 ^ (prefixWord ++ tailWord_274324).sum := by decide
  have hdescent : baseEnd_274324 < baseStart_274324 := by decide
  rcases family_descends (prefixWord ++ tailWord_274324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274343 : List Nat := [1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_274343 : Nat := 118140960795 + 274343 * 2 ^ 59
def prefixEnd_274343 : Nat := 4983230072969 + 3 ^ 40 * 274343 * 2
def baseEnd_274343 : Nat := 83478413746089105452341

theorem tailTrace_274343 : CollatzResearch.WordTrace tailWord_274343 prefixEnd_274343 83478413746089105452341 := by
  unfold tailWord_274343
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006111245109639899267683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6670740830073093266178455 10006111245109639899267683)
  ·
    refine ⟨15009166867664459848901525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10006111245109639899267683 15009166867664459848901525)
    ·
      refine ⟨703554696921771555417259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15009166867664459848901525 703554696921771555417259)
      ·
        refine ⟨1055332045382657333125889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703554696921771555417259 1055332045382657333125889)
        ·
          refine ⟨791499034036992999844417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055332045382657333125889 791499034036992999844417)
          ·
            refine ⟨593624275527744749883313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791499034036992999844417 593624275527744749883313)
            ·
              refine ⟨445218206645808562412485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593624275527744749883313 445218206645808562412485)
              ·
                refine ⟨83478413746089105452341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445218206645808562412485 83478413746089105452341)
                ·
                  rfl

theorem cell19_274343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_274343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274343 prefixEnd_274343 := by exact prefixLift 274343
  have htrace : WordTrace (prefixWord ++ tailWord_274343) baseStart_274343 baseEnd_274343 := by
    simpa [prefixWord, tailWord_274343, baseEnd_274343] using wordTrace_append hprefix tailTrace_274343
  have hstable : (prefixWord ++ tailWord_274343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274343).length < 2 ^ (prefixWord ++ tailWord_274343).sum := by decide
  have hdescent : baseEnd_274343 < baseStart_274343 := by decide
  rcases family_descends (prefixWord ++ tailWord_274343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274381 : List Nat := [1, 6, 3, 9]
def baseStart_274381 : Nat := 118140960795 + 274381 * 2 ^ 59
def prefixEnd_274381 : Nat := 4983230072969 + 3 ^ 40 * 274381 * 2
def baseEnd_274381 : Nat := 1030740451477978723553

theorem tailTrace_274381 : CollatzResearch.WordTrace tailWord_274381 prefixEnd_274381 1030740451477978723553 := by
  unfold tailWord_274381
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007497218971972389150997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6671664812647981592767331 10007497218971972389150997)
  ·
    refine ⟨469101432139311205741453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10007497218971972389150997 469101432139311205741453)
    ·
      refine ⟨175913037052241702153045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 469101432139311205741453 175913037052241702153045)
      ·
        refine ⟨1030740451477978723553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 175913037052241702153045 1030740451477978723553)
        ·
          rfl

theorem cell19_274381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 9].length) (baseStart_274381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274381 prefixEnd_274381 := by exact prefixLift 274381
  have htrace : WordTrace (prefixWord ++ tailWord_274381) baseStart_274381 baseEnd_274381 := by
    simpa [prefixWord, tailWord_274381, baseEnd_274381] using wordTrace_append hprefix tailTrace_274381
  have hstable : (prefixWord ++ tailWord_274381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274381).length < 2 ^ (prefixWord ++ tailWord_274381).sum := by decide
  have hdescent : baseEnd_274381 < baseStart_274381 := by decide
  rcases family_descends (prefixWord ++ tailWord_274381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274472 : List Nat := [2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_274472 : Nat := 118140960795 + 274472 * 2 ^ 59
def prefixEnd_274472 : Nat := 4983230072969 + 3 ^ 40 * 274472 * 2
def baseEnd_274472 : Nat := 83517666489455028585323

theorem tailTrace_274472 : CollatzResearch.WordTrace tailWord_274472 prefixEnd_274472 83517666489455028585323 := by
  unfold tailWord_274472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5005408130821147465356835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6673877507761529953809113 5005408130821147465356835)
  ·
    refine ⟨7508112196231721198035253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5005408130821147465356835 7508112196231721198035253)
    ·
      refine ⟨703885518396723862315805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7508112196231721198035253 703885518396723862315805)
      ·
        refine ⟨263957069398771448368427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 703885518396723862315805 263957069398771448368427)
        ·
          refine ⟨395935604098157172552641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263957069398771448368427 395935604098157172552641)
          ·
            refine ⟨296951703073617879414481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395935604098157172552641 296951703073617879414481)
            ·
              refine ⟨222713777305213409560861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296951703073617879414481 222713777305213409560861)
              ·
                refine ⟨83517666489455028585323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222713777305213409560861 83517666489455028585323)
                ·
                  rfl

theorem cell19_274472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_274472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274472 prefixEnd_274472 := by exact prefixLift 274472
  have htrace : WordTrace (prefixWord ++ tailWord_274472) baseStart_274472 baseEnd_274472 := by
    simpa [prefixWord, tailWord_274472, baseEnd_274472] using wordTrace_append hprefix tailTrace_274472
  have hstable : (prefixWord ++ tailWord_274472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274472).length < 2 ^ (prefixWord ++ tailWord_274472).sum := by decide
  have hdescent : baseEnd_274472 < baseStart_274472 := by decide
  rcases family_descends (prefixWord ++ tailWord_274472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274474 : List Nat := [3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_274474 : Nat := 118140960795 + 274474 * 2 ^ 59
def prefixEnd_274474 : Nat := 4983230072969 + 3 ^ 40 * 274474 * 2
def baseEnd_274474 : Nat := 83518275059119616540873

theorem tailTrace_274474 : CollatzResearch.WordTrace tailWord_274474 prefixEnd_274474 83518275059119616540873 := by
  unfold tailWord_274474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502722301908762318071619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6673926138423366181524317 2502722301908762318071619)
  ·
    refine ⟨3754083452863143477107429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2502722301908762318071619 3754083452863143477107429)
    ·
      refine ⟨703890647411839401957643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3754083452863143477107429 703890647411839401957643)
      ·
        refine ⟨1055835971117759102936465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703890647411839401957643 1055835971117759102936465)
        ·
          refine ⟨791876978338319327202349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055835971117759102936465 791876978338319327202349)
          ·
            refine ⟨296953866876869747700881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 791876978338319327202349 296953866876869747700881)
            ·
              refine ⟨222715400157652310775661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296953866876869747700881 222715400157652310775661)
              ·
                refine ⟨83518275059119616540873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222715400157652310775661 83518275059119616540873)
                ·
                  rfl

theorem cell19_274474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_274474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274474 prefixEnd_274474 := by exact prefixLift 274474
  have htrace : WordTrace (prefixWord ++ tailWord_274474) baseStart_274474 baseEnd_274474 := by
    simpa [prefixWord, tailWord_274474, baseEnd_274474] using wordTrace_append hprefix tailTrace_274474
  have hstable : (prefixWord ++ tailWord_274474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274474).length < 2 ^ (prefixWord ++ tailWord_274474).sum := by decide
  have hdescent : baseEnd_274474 < baseStart_274474 := by decide
  rcases family_descends (prefixWord ++ tailWord_274474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274497 : List Nat := [1, 2, 5, 1, 2, 1, 7]
def baseStart_274497 : Nat := 118140960795 + 274497 * 2 ^ 59
def prefixEnd_274497 : Nat := 4983230072969 + 3 ^ 40 * 274497 * 2
def baseEnd_274497 : Nat := 27841757870087459343233

theorem tailTrace_274497 : CollatzResearch.WordTrace tailWord_274497 prefixEnd_274497 27841757870087459343233 := by
  unfold tailWord_274497
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011728086551724200373745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6674485391034482800249163 10011728086551724200373745)
  ·
    refine ⟨7508796064913793150280309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10011728086551724200373745 7508796064913793150280309)
    ·
      refine ⟨703949631085668107838779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7508796064913793150280309 703949631085668107838779)
      ·
        refine ⟨1055924446628502161758169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703949631085668107838779 1055924446628502161758169)
        ·
          refine ⟨791943334971376621318627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055924446628502161758169 791943334971376621318627)
          ·
            refine ⟨1187915002457064931977941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791943334971376621318627 1187915002457064931977941)
            ·
              refine ⟨27841757870087459343233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1187915002457064931977941 27841757870087459343233)
              ·
                rfl

theorem cell19_274497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_274497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274497 prefixEnd_274497 := by exact prefixLift 274497
  have htrace : WordTrace (prefixWord ++ tailWord_274497) baseStart_274497 baseEnd_274497 := by
    simpa [prefixWord, tailWord_274497, baseEnd_274497] using wordTrace_append hprefix tailTrace_274497
  have hstable : (prefixWord ++ tailWord_274497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274497).length < 2 ^ (prefixWord ++ tailWord_274497).sum := by decide
  have hdescent : baseEnd_274497 < baseStart_274497 := by decide
  rcases family_descends (prefixWord ++ tailWord_274497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274514 : List Nat := [3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_274514 : Nat := 118140960795 + 274514 * 2 ^ 59
def prefixEnd_274514 : Nat := 4983230072969 + 3 ^ 40 * 274514 * 2
def baseEnd_274514 : Nat := 83530446452411375651875

theorem tailTrace_274514 : CollatzResearch.WordTrace tailWord_274514 prefixEnd_274514 83530446452411375651875 := by
  unfold tailWord_274514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503087031872534025935649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6674898751660090735828397 2503087031872534025935649)
  ·
    refine ⟨1877315273904400519451737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2503087031872534025935649 1877315273904400519451737)
    ·
      refine ⟨1407986455428300389588803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1877315273904400519451737 1407986455428300389588803)
      ·
        refine ⟨2111979683142450584383205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407986455428300389588803 2111979683142450584383205)
        ·
          refine ⟨395996190589209484571851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2111979683142450584383205 395996190589209484571851)
          ·
            refine ⟨593994285883814226857777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395996190589209484571851 593994285883814226857777)
            ·
              refine ⟨445495714412860670143333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593994285883814226857777 445495714412860670143333)
              ·
                refine ⟨83530446452411375651875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445495714412860670143333 83530446452411375651875)
                ·
                  rfl

theorem cell19_274514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_274514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274514 prefixEnd_274514 := by exact prefixLift 274514
  have htrace : WordTrace (prefixWord ++ tailWord_274514) baseStart_274514 baseEnd_274514 := by
    simpa [prefixWord, tailWord_274514, baseEnd_274514] using wordTrace_append hprefix tailTrace_274514
  have hstable : (prefixWord ++ tailWord_274514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274514).length < 2 ^ (prefixWord ++ tailWord_274514).sum := by decide
  have hdescent : baseEnd_274514 < baseStart_274514 := by decide
  rcases family_descends (prefixWord ++ tailWord_274514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274537 : List Nat := [1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_274537 : Nat := 118140960795 + 274537 * 2 ^ 59
def prefixEnd_274537 : Nat := 4983230072969 + 3 ^ 40 * 274537 * 2
def baseEnd_274537 : Nat := 83537445003554137140701

theorem tailTrace_274537 : CollatzResearch.WordTrace tailWord_274537 prefixEnd_274537 83537445003554137140701 := by
  unfold tailWord_274537
  simp only [CollatzResearch.WordTrace]
  refine ⟨10013187006406811031829865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6675458004271207354553243 10013187006406811031829865)
  ·
    refine ⟨7509890254805108273872399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10013187006406811031829865 7509890254805108273872399)
    ·
      refine ⟨11264835382207662410808599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509890254805108273872399 11264835382207662410808599)
      ·
        refine ⟨16897253073311493616212899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11264835382207662410808599 16897253073311493616212899)
        ·
          refine ⟨25345879609967240424319349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16897253073311493616212899 25345879609967240424319349)
          ·
            refine ⟨2376176213434428789779939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25345879609967240424319349 2376176213434428789779939)
            ·
              refine ⟨3564264320151643184669909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376176213434428789779939 3564264320151643184669909)
              ·
                refine ⟨83537445003554137140701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3564264320151643184669909 83537445003554137140701)
                ·
                  rfl

theorem cell19_274537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_274537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274537 prefixEnd_274537 := by exact prefixLift 274537
  have htrace : WordTrace (prefixWord ++ tailWord_274537) baseStart_274537 baseEnd_274537 := by
    simpa [prefixWord, tailWord_274537, baseEnd_274537] using wordTrace_append hprefix tailTrace_274537
  have hstable : (prefixWord ++ tailWord_274537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274537).length < 2 ^ (prefixWord ++ tailWord_274537).sum := by decide
  have hdescent : baseEnd_274537 < baseStart_274537 := by decide
  rcases family_descends (prefixWord ++ tailWord_274537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274556 : List Nat := [2, 2, 2, 1, 1, 11]
def baseStart_274556 : Nat := 118140960795 + 274556 * 2 ^ 59
def prefixEnd_274556 : Nat := 4983230072969 + 3 ^ 40 * 274556 * 2
def baseEnd_274556 : Nat := 9282580712818635857603

theorem tailTrace_274556 : CollatzResearch.WordTrace tailWord_274556 prefixEnd_274556 9282580712818635857603 := by
  unfold tailWord_274556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006939996668988638385761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6675919995558651517847681 5006939996668988638385761)
  ·
    refine ⟨3755204997501741478789321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5006939996668988638385761 3755204997501741478789321)
    ·
      refine ⟨2816403748126306109091991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3755204997501741478789321 2816403748126306109091991)
      ·
        refine ⟨4224605622189459163637987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816403748126306109091991 4224605622189459163637987)
        ·
          refine ⟨6336908433284188745456981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224605622189459163637987 6336908433284188745456981)
          ·
            refine ⟨9282580712818635857603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6336908433284188745456981 9282580712818635857603)
            ·
              rfl

theorem cell19_274556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_274556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274556 prefixEnd_274556 := by exact prefixLift 274556
  have htrace : WordTrace (prefixWord ++ tailWord_274556) baseStart_274556 baseEnd_274556 := by
    simpa [prefixWord, tailWord_274556, baseEnd_274556] using wordTrace_append hprefix tailTrace_274556
  have hstable : (prefixWord ++ tailWord_274556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274556).length < 2 ^ (prefixWord ++ tailWord_274556).sum := by decide
  have hdescent : baseEnd_274556 < baseStart_274556 := by decide
  rcases family_descends (prefixWord ++ tailWord_274556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274582 : List Nat := [5, 3, 2, 1, 1, 1, 3, 3]
def baseStart_274582 : Nat := 118140960795 + 274582 * 2 ^ 59
def prefixEnd_274582 : Nat := 4983230072969 + 3 ^ 40 * 274582 * 2
def baseEnd_274582 : Nat := 83551137821007366140579

theorem tailTrace_274582 : CollatzResearch.WordTrace tailWord_274582 prefixEnd_274582 83551137821007366140579 := by
  unfold tailWord_274582
  simp only [CollatzResearch.WordTrace]
  refine ⟨625926768202736482326125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6676552194162522478145333 625926768202736482326125)
  ·
    refine ⟨234722538076026180872297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 625926768202736482326125 234722538076026180872297)
    ·
      refine ⟨176041903557019635654223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234722538076026180872297 176041903557019635654223)
      ·
        refine ⟨264062855335529453481335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176041903557019635654223 264062855335529453481335)
        ·
          refine ⟨396094283003294180222003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264062855335529453481335 396094283003294180222003)
          ·
            refine ⟨594141424504941270333005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396094283003294180222003 594141424504941270333005)
            ·
              refine ⟨222803034189352976374877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594141424504941270333005 222803034189352976374877)
              ·
                refine ⟨83551137821007366140579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222803034189352976374877 83551137821007366140579)
                ·
                  rfl

theorem cell19_274582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_274582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274582 prefixEnd_274582 := by exact prefixLift 274582
  have htrace : WordTrace (prefixWord ++ tailWord_274582) baseStart_274582 baseEnd_274582 := by
    simpa [prefixWord, tailWord_274582, baseEnd_274582] using wordTrace_append hprefix tailTrace_274582
  have hstable : (prefixWord ++ tailWord_274582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274582).length < 2 ^ (prefixWord ++ tailWord_274582).sum := by decide
  have hdescent : baseEnd_274582 < baseStart_274582 := by decide
  rcases family_descends (prefixWord ++ tailWord_274582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274632 : List Nat := [2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_274632 : Nat := 118140960795 + 274632 * 2 ^ 59
def prefixEnd_274632 : Nat := 4983230072969 + 3 ^ 40 * 274632 * 2
def baseEnd_274632 : Nat := 83566352062622065029331

theorem tailTrace_274632 : CollatzResearch.WordTrace tailWord_274632 prefixEnd_274632 83566352062622065029331 := by
  unfold tailWord_274632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008325970531321128269075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6677767960708428171025433 5008325970531321128269075)
  ·
    refine ⟨7512488955796981692403613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5008325970531321128269075 7512488955796981692403613)
    ·
      refine ⟨2817183358423868134651355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7512488955796981692403613 2817183358423868134651355)
      ·
        refine ⟨4225775037635802201977033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817183358423868134651355 4225775037635802201977033)
        ·
          refine ⟨3169331278226851651482775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4225775037635802201977033 3169331278226851651482775)
          ·
            refine ⟨4753996917340277477224163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169331278226851651482775 4753996917340277477224163)
            ·
              refine ⟨7130995376010416215836245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753996917340277477224163 7130995376010416215836245)
              ·
                refine ⟨83566352062622065029331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7130995376010416215836245 83566352062622065029331)
                ·
                  rfl

theorem cell19_274632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_274632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274632 prefixEnd_274632 := by exact prefixLift 274632
  have htrace : WordTrace (prefixWord ++ tailWord_274632) baseStart_274632 baseEnd_274632 := by
    simpa [prefixWord, tailWord_274632, baseEnd_274632] using wordTrace_append hprefix tailTrace_274632
  have hstable : (prefixWord ++ tailWord_274632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274632).length < 2 ^ (prefixWord ++ tailWord_274632).sum := by decide
  have hdescent : baseEnd_274632 < baseStart_274632 := by decide
  rcases family_descends (prefixWord ++ tailWord_274632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274645 : List Nat := [1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_274645 : Nat := 118140960795 + 274645 * 2 ^ 59
def prefixEnd_274645 : Nat := 4983230072969 + 3 ^ 40 * 274645 * 2
def baseEnd_274645 : Nat := 83570307765441886740407

theorem tailTrace_274645 : CollatzResearch.WordTrace tailWord_274645 prefixEnd_274645 83570307765441886740407 := by
  unfold tailWord_274645
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017126090015545476761389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6678084060010363651174259 10017126090015545476761389)
  ·
    refine ⟨3756422283755829553785521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10017126090015545476761389 3756422283755829553785521)
    ·
      refine ⟨2817316712816872165339141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3756422283755829553785521 2817316712816872165339141)
      ·
        refine ⟨528246883653163531001089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2817316712816872165339141 528246883653163531001089)
        ·
          refine ⟨396185162739872648250817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528246883653163531001089 396185162739872648250817)
          ·
            refine ⟨297138872054904486188113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396185162739872648250817 297138872054904486188113)
            ·
              refine ⟨222854154041178364641085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297138872054904486188113 222854154041178364641085)
              ·
                refine ⟨83570307765441886740407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222854154041178364641085 83570307765441886740407)
                ·
                  rfl

theorem cell19_274645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_274645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274645 prefixEnd_274645 := by exact prefixLift 274645
  have htrace : WordTrace (prefixWord ++ tailWord_274645) baseStart_274645 baseEnd_274645 := by
    simpa [prefixWord, tailWord_274645, baseEnd_274645] using wordTrace_append hprefix tailTrace_274645
  have hstable : (prefixWord ++ tailWord_274645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274645).length < 2 ^ (prefixWord ++ tailWord_274645).sum := by decide
  have hdescent : baseEnd_274645 < baseStart_274645 := by decide
  rcases family_descends (prefixWord ++ tailWord_274645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274649 : List Nat := [1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_274649 : Nat := 118140960795 + 274649 * 2 ^ 59
def prefixEnd_274649 : Nat := 4983230072969 + 3 ^ 40 * 274649 * 2
def baseEnd_274649 : Nat := 83571524904771062651507

theorem tailTrace_274649 : CollatzResearch.WordTrace tailWord_274649 prefixEnd_274649 83571524904771062651507 := by
  unfold tailWord_274649
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017271982001054159907001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6678181321334036106604667 10017271982001054159907001)
  ·
    refine ⟨7512953986500790619930251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10017271982001054159907001 7512953986500790619930251)
    ·
      refine ⟨11269430979751185929895377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7512953986500790619930251 11269430979751185929895377)
      ·
        refine ⟨8452073234813389447421533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11269430979751185929895377 8452073234813389447421533)
        ·
          refine ⟨3169527463055021042783075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8452073234813389447421533 3169527463055021042783075)
          ·
            refine ⟨4754291194582531564174613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169527463055021042783075 4754291194582531564174613)
            ·
              refine ⟨222857399746056167070685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4754291194582531564174613 222857399746056167070685)
              ·
                refine ⟨83571524904771062651507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222857399746056167070685 83571524904771062651507)
                ·
                  rfl

theorem cell19_274649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_274649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274649 prefixEnd_274649 := by exact prefixLift 274649
  have htrace : WordTrace (prefixWord ++ tailWord_274649) baseStart_274649 baseEnd_274649 := by
    simpa [prefixWord, tailWord_274649, baseEnd_274649] using wordTrace_append hprefix tailTrace_274649
  have hstable : (prefixWord ++ tailWord_274649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274649).length < 2 ^ (prefixWord ++ tailWord_274649).sum := by decide
  have hdescent : baseEnd_274649 < baseStart_274649 := by decide
  rcases family_descends (prefixWord ++ tailWord_274649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274725 : List Nat := [1, 3, 1, 2, 6, 6]
def baseStart_274725 : Nat := 118140960795 + 274725 * 2 ^ 59
def prefixEnd_274725 : Nat := 4983230072969 + 3 ^ 40 * 274725 * 2
def baseEnd_274725 : Nat := 9288294505780600551379

theorem tailTrace_274725 : CollatzResearch.WordTrace tailWord_274725 prefixEnd_274725 9288294505780600551379 := by
  unfold tailWord_274725
  simp only [CollatzResearch.WordTrace]
  refine ⟨10020043929725719139673629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6680029286483812759782419 10020043929725719139673629)
  ·
    refine ⟨3757516473647144677377611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10020043929725719139673629 3757516473647144677377611)
    ·
      refine ⟨5636274710470717016066417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757516473647144677377611 5636274710470717016066417)
      ·
        refine ⟨4227206032853037762049813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5636274710470717016066417 4227206032853037762049813)
        ·
          refine ⟨198150282789986145096085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4227206032853037762049813 198150282789986145096085)
          ·
            refine ⟨9288294505780600551379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 198150282789986145096085 9288294505780600551379)
            ·
              rfl

theorem cell19_274725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_274725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274725 prefixEnd_274725 := by exact prefixLift 274725
  have htrace : WordTrace (prefixWord ++ tailWord_274725) baseStart_274725 baseEnd_274725 := by
    simpa [prefixWord, tailWord_274725, baseEnd_274725] using wordTrace_append hprefix tailTrace_274725
  have hstable : (prefixWord ++ tailWord_274725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274725).length < 2 ^ (prefixWord ++ tailWord_274725).sum := by decide
  have hdescent : baseEnd_274725 < baseStart_274725 := by decide
  rcases family_descends (prefixWord ++ tailWord_274725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274780 : List Nat := [2, 2, 4, 3, 1, 1, 6]
def baseStart_274780 : Nat := 118140960795 + 274780 * 2 ^ 59
def prefixEnd_274780 : Nat := 4983230072969 + 3 ^ 40 * 274780 * 2
def baseEnd_274780 : Nat := 27870462072600524580013

theorem tailTrace_274780 : CollatzResearch.WordTrace tailWord_274780 prefixEnd_274780 27870462072600524580013 := by
  unfold tailWord_274780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011024972263231766462897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6681366629684309021950529 5011024972263231766462897)
  ·
    refine ⟨3758268729197423824847173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5011024972263231766462897 3758268729197423824847173)
    ·
      refine ⟨704675386724516967158845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3758268729197423824847173 704675386724516967158845)
      ·
        refine ⟨264253270021693862684567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 704675386724516967158845 264253270021693862684567)
        ·
          refine ⟨396379905032540794026851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264253270021693862684567 396379905032540794026851)
          ·
            refine ⟨594569857548811191040277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396379905032540794026851 594569857548811191040277)
            ·
              refine ⟨27870462072600524580013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 594569857548811191040277 27870462072600524580013)
              ·
                rfl

theorem cell19_274780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_274780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274780 prefixEnd_274780 := by exact prefixLift 274780
  have htrace : WordTrace (prefixWord ++ tailWord_274780) baseStart_274780 baseEnd_274780 := by
    simpa [prefixWord, tailWord_274780, baseEnd_274780] using wordTrace_append hprefix tailTrace_274780
  have hstable : (prefixWord ++ tailWord_274780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274780).length < 2 ^ (prefixWord ++ tailWord_274780).sum := by decide
  have hdescent : baseEnd_274780 < baseStart_274780 := by decide
  rcases family_descends (prefixWord ++ tailWord_274780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274856 : List Nat := [2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_274856 : Nat := 118140960795 + 274856 * 2 ^ 59
def prefixEnd_274856 : Nat := 4983230072969 + 3 ^ 40 * 274856 * 2
def baseEnd_274856 : Nat := 83634511865055916050943

theorem tailTrace_274856 : CollatzResearch.WordTrace tailWord_274856 prefixEnd_274856 83634511865055916050943 := by
  unfold tailWord_274856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012410946125564256346211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6683214594834085675128281 5012410946125564256346211)
  ·
    refine ⟨7518616419188346384519317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5012410946125564256346211 7518616419188346384519317)
    ·
      refine ⟨352435144649453736774343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7518616419188346384519317 352435144649453736774343)
      ·
        refine ⟨528652716974180605161515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352435144649453736774343 528652716974180605161515)
        ·
          refine ⟨792979075461270907742273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528652716974180605161515 792979075461270907742273)
          ·
            refine ⟨594734306595953180806705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792979075461270907742273 594734306595953180806705)
            ·
              refine ⟨446050729946964885605029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594734306595953180806705 446050729946964885605029)
              ·
                refine ⟨83634511865055916050943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446050729946964885605029 83634511865055916050943)
                ·
                  rfl

theorem cell19_274856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_274856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274856 prefixEnd_274856 := by exact prefixLift 274856
  have htrace : WordTrace (prefixWord ++ tailWord_274856) baseStart_274856 baseEnd_274856 := by
    simpa [prefixWord, tailWord_274856, baseEnd_274856] using wordTrace_append hprefix tailTrace_274856
  have hstable : (prefixWord ++ tailWord_274856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274856).length < 2 ^ (prefixWord ++ tailWord_274856).sum := by decide
  have hdescent : baseEnd_274856 < baseStart_274856 := by decide
  rcases family_descends (prefixWord ++ tailWord_274856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274955 : List Nat := [1, 1, 1, 1, 7, 2, 6]
def baseStart_274955 : Nat := 118140960795 + 274955 * 2 ^ 59
def prefixEnd_274955 : Nat := 4983230072969 + 3 ^ 40 * 274955 * 2
def baseEnd_274955 : Nat := 27888212021151006616891

theorem tailTrace_274955 : CollatzResearch.WordTrace tailWord_274955 prefixEnd_274955 27888212021151006616891 := by
  unfold tailWord_274955
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028432718892468420546319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6685621812594978947030879 10028432718892468420546319)
  ·
    refine ⟨15042649078338702630819479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10028432718892468420546319 15042649078338702630819479)
    ·
      refine ⟨22563973617508053946229219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15042649078338702630819479 22563973617508053946229219)
      ·
        refine ⟨33845960426262080919343829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22563973617508053946229219 33845960426262080919343829)
        ·
          refine ⟨793264697490517521547121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33845960426262080919343829 793264697490517521547121)
          ·
            refine ⟨594948523117888141160341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793264697490517521547121 594948523117888141160341)
            ·
              refine ⟨27888212021151006616891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 594948523117888141160341 27888212021151006616891)
              ·
                rfl

theorem cell19_274955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_274955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_274955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_274955 prefixEnd_274955 := by exact prefixLift 274955
  have htrace : WordTrace (prefixWord ++ tailWord_274955) baseStart_274955 baseEnd_274955 := by
    simpa [prefixWord, tailWord_274955, baseEnd_274955] using wordTrace_append hprefix tailTrace_274955
  have hstable : (prefixWord ++ tailWord_274955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274955).length < 2 ^ (prefixWord ++ tailWord_274955).sum := by decide
  have hdescent : baseEnd_274955 < baseStart_274955 := by decide
  rcases family_descends (prefixWord ++ tailWord_274955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275006 : List Nat := [4, 2, 1, 4, 2, 1, 5]
def baseStart_275006 : Nat := 118140960795 + 275006 * 2 ^ 59
def prefixEnd_275006 : Nat := 4983230072969 + 3 ^ 40 * 275006 * 2
def baseEnd_275006 : Nat := 27893384863300004239067

theorem tailTrace_275006 : CollatzResearch.WordTrace tailWord_275006 prefixEnd_275006 27893384863300004239067 := by
  unfold tailWord_275006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253786605213463016331609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6686861894471802753768581 1253786605213463016331609)
  ·
    refine ⟨940339953910097262248707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1253786605213463016331609 940339953910097262248707)
    ·
      refine ⟨1410509930865145893373061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 940339953910097262248707 1410509930865145893373061)
      ·
        refine ⟨264470612037214855007449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1410509930865145893373061 264470612037214855007449)
        ·
          refine ⟨198352959027911141255587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264470612037214855007449 198352959027911141255587)
          ·
            refine ⟨297529438541866711883381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198352959027911141255587 297529438541866711883381)
            ·
              refine ⟨27893384863300004239067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 297529438541866711883381 27893384863300004239067)
              ·
                rfl

theorem cell19_275006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_275006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275006 prefixEnd_275006 := by exact prefixLift 275006
  have htrace : WordTrace (prefixWord ++ tailWord_275006) baseStart_275006 baseEnd_275006 := by
    simpa [prefixWord, tailWord_275006, baseEnd_275006] using wordTrace_append hprefix tailTrace_275006
  have hstable : (prefixWord ++ tailWord_275006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275006).length < 2 ^ (prefixWord ++ tailWord_275006).sum := by decide
  have hdescent : baseEnd_275006 < baseStart_275006 := by decide
  rcases family_descends (prefixWord ++ tailWord_275006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275031 : List Nat := [1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_275031 : Nat := 118140960795 + 275031 * 2 ^ 59
def prefixEnd_275031 : Nat := 4983230072969 + 3 ^ 40 * 275031 * 2
def baseEnd_275031 : Nat := 83687761710707362161577

theorem tailTrace_275031 : CollatzResearch.WordTrace tailWord_275031 prefixEnd_275031 83687761710707362161577 := by
  unfold tailWord_275031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10031204666617133400312947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6687469777744755600208631 10031204666617133400312947)
  ·
    refine ⟨15046806999925700100469421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10031204666617133400312947 15046806999925700100469421)
    ·
      refine ⟨5642552624972137537676033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15046806999925700100469421 5642552624972137537676033)
      ·
        refine ⟨4231914468729103153257025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5642552624972137537676033 4231914468729103153257025)
        ·
          refine ⟨3173935851546827364942769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231914468729103153257025 3173935851546827364942769)
          ·
            refine ⟨2380451888660120523707077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3173935851546827364942769 2380451888660120523707077)
            ·
              refine ⟨446334729123772598195077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2380451888660120523707077 446334729123772598195077)
              ·
                refine ⟨83687761710707362161577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446334729123772598195077 83687761710707362161577)
                ·
                  rfl

theorem cell19_275031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_275031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275031 prefixEnd_275031 := by exact prefixLift 275031
  have htrace : WordTrace (prefixWord ++ tailWord_275031) baseStart_275031 baseEnd_275031 := by
    simpa [prefixWord, tailWord_275031, baseEnd_275031] using wordTrace_append hprefix tailTrace_275031
  have hstable : (prefixWord ++ tailWord_275031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275031).length < 2 ^ (prefixWord ++ tailWord_275031).sum := by decide
  have hdescent : baseEnd_275031 < baseStart_275031 := by decide
  rcases family_descends (prefixWord ++ tailWord_275031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275050 : List Nat := [3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_275050 : Nat := 118140960795 + 275050 * 2 ^ 59
def prefixEnd_275050 : Nat := 4983230072969 + 3 ^ 40 * 275050 * 2
def baseEnd_275050 : Nat := 83693543122520947739303

theorem tailTrace_275050 : CollatzResearch.WordTrace tailWord_275050 prefixEnd_275050 83693543122520947739303 := by
  unfold tailWord_275050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507974413387074911313651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6687931769032199763503069 2507974413387074911313651)
  ·
    refine ⟨3761961620080612366970477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2507974413387074911313651 3761961620080612366970477)
    ·
      refine ⟨1410735607530229637613929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3761961620080612366970477 1410735607530229637613929)
      ·
        refine ⟨1058051705647672228210447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1410735607530229637613929 1058051705647672228210447)
        ·
          refine ⟨1587077558471508342315671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058051705647672228210447 1587077558471508342315671)
          ·
            refine ⟨2380616337707262513473507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587077558471508342315671 2380616337707262513473507)
            ·
              refine ⟨3570924506560893770210261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380616337707262513473507 3570924506560893770210261)
              ·
                refine ⟨83693543122520947739303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3570924506560893770210261 83693543122520947739303)
                ·
                  rfl

theorem cell19_275050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_275050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275050 prefixEnd_275050 := by exact prefixLift 275050
  have htrace : WordTrace (prefixWord ++ tailWord_275050) baseStart_275050 baseEnd_275050 := by
    simpa [prefixWord, tailWord_275050, baseEnd_275050] using wordTrace_append hprefix tailTrace_275050
  have hstable : (prefixWord ++ tailWord_275050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275050).length < 2 ^ (prefixWord ++ tailWord_275050).sum := by decide
  have hdescent : baseEnd_275050 < baseStart_275050 := by decide
  rcases family_descends (prefixWord ++ tailWord_275050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275069 : List Nat := [1, 4, 1, 1, 5, 7]
def baseStart_275069 : Nat := 118140960795 + 275069 * 2 ^ 59
def prefixEnd_275069 : Nat := 4983230072969 + 3 ^ 40 * 275069 * 2
def baseEnd_275069 : Nat := 9299924948259392590781

theorem tailTrace_275069 : CollatzResearch.WordTrace tailWord_275069 prefixEnd_275069 9299924948259392590781 := by
  unfold tailWord_275069
  simp only [CollatzResearch.WordTrace]
  refine ⟨10032590640479465890196261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6688393760319643926797507 10032590640479465890196261)
  ·
    refine ⟨1881110745089899854411799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10032590640479465890196261 1881110745089899854411799)
    ·
      refine ⟨2821666117634849781617699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881110745089899854411799 2821666117634849781617699)
      ·
        refine ⟨4232499176452274672426549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821666117634849781617699 4232499176452274672426549)
        ·
          refine ⟨396796797792400750539989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4232499176452274672426549 396796797792400750539989)
          ·
            refine ⟨9299924948259392590781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 396796797792400750539989 9299924948259392590781)
            ·
              rfl

theorem cell19_275069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_275069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275069 prefixEnd_275069 := by exact prefixLift 275069
  have htrace : WordTrace (prefixWord ++ tailWord_275069) baseStart_275069 baseEnd_275069 := by
    simpa [prefixWord, tailWord_275069, baseEnd_275069] using wordTrace_append hprefix tailTrace_275069
  have hstable : (prefixWord ++ tailWord_275069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275069).length < 2 ^ (prefixWord ++ tailWord_275069).sum := by decide
  have hdescent : baseEnd_275069 < baseStart_275069 := by decide
  rcases family_descends (prefixWord ++ tailWord_275069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275183 : List Nat := [1, 1, 2, 1, 5, 4, 5]
def baseStart_275183 : Nat := 118140960795 + 275183 * 2 ^ 59
def prefixEnd_275183 : Nat := 4983230072969 + 3 ^ 40 * 275183 * 2
def baseEnd_275183 : Nat := 27911337668405348927795

theorem tailTrace_275183 : CollatzResearch.WordTrace tailWord_275183 prefixEnd_275183 27911337668405348927795 := by
  unfold tailWord_275183
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036748562066463359846203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6691165708044308906564135 10036748562066463359846203)
  ·
    refine ⟨15055122843099695039769305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10036748562066463359846203 15055122843099695039769305)
    ·
      refine ⟨11291342132324771279826979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15055122843099695039769305 11291342132324771279826979)
      ·
        refine ⟨16937013198487156919740469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11291342132324771279826979 16937013198487156919740469)
        ·
          refine ⟨1587844987358170961225669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16937013198487156919740469 1587844987358170961225669)
          ·
            refine ⟨297720935129657055229813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1587844987358170961225669 297720935129657055229813)
            ·
              refine ⟨27911337668405348927795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 297720935129657055229813 27911337668405348927795)
              ·
                rfl

theorem cell19_275183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_275183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275183 prefixEnd_275183 := by exact prefixLift 275183
  have htrace : WordTrace (prefixWord ++ tailWord_275183) baseStart_275183 baseEnd_275183 := by
    simpa [prefixWord, tailWord_275183, baseEnd_275183] using wordTrace_append hprefix tailTrace_275183
  have hstable : (prefixWord ++ tailWord_275183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275183).length < 2 ^ (prefixWord ++ tailWord_275183).sum := by decide
  have hdescent : baseEnd_275183 < baseStart_275183 := by decide
  rcases family_descends (prefixWord ++ tailWord_275183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275276 : List Nat := [2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_275276 : Nat := 118140960795 + 275276 * 2 ^ 59
def prefixEnd_275276 : Nat := 4983230072969 + 3 ^ 40 * 275276 * 2
def baseEnd_275276 : Nat := 83762311494619386716465

theorem tailTrace_275276 : CollatzResearch.WordTrace tailWord_275276 prefixEnd_275276 83762311494619386716465 := by
  unfold tailWord_275276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020070275364770121490841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6693427033819693495321121 5020070275364770121490841)
  ·
    refine ⟨3765052706523577591118131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5020070275364770121490841 3765052706523577591118131)
    ·
      refine ⟨5647579059785366386677197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765052706523577591118131 5647579059785366386677197)
      ·
        refine ⟨2117842147419512395003949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5647579059785366386677197 2117842147419512395003949)
        ·
          refine ⟨794190805282317148126481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2117842147419512395003949 794190805282317148126481)
          ·
            refine ⟨595643103961737861094861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794190805282317148126481 595643103961737861094861)
            ·
              refine ⟨223366163985651697910573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 595643103961737861094861 223366163985651697910573)
              ·
                refine ⟨83762311494619386716465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223366163985651697910573 83762311494619386716465)
                ·
                  rfl

theorem cell19_275276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_275276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275276 prefixEnd_275276 := by exact prefixLift 275276
  have htrace : WordTrace (prefixWord ++ tailWord_275276) baseStart_275276 baseEnd_275276 := by
    simpa [prefixWord, tailWord_275276, baseEnd_275276] using wordTrace_append hprefix tailTrace_275276
  have hstable : (prefixWord ++ tailWord_275276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275276).length < 2 ^ (prefixWord ++ tailWord_275276).sum := by decide
  have hdescent : baseEnd_275276 < baseStart_275276 := by decide
  rcases family_descends (prefixWord ++ tailWord_275276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275280 : List Nat := [2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_275280 : Nat := 118140960795 + 275280 * 2 ^ 59
def prefixEnd_275280 : Nat := 4983230072969 + 3 ^ 40 * 275280 * 2
def baseEnd_275280 : Nat := 83763528633948562627565

theorem tailTrace_275280 : CollatzResearch.WordTrace tailWord_275280 prefixEnd_275280 83763528633948562627565 := by
  unfold tailWord_275280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020143221357524463063647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6693524295143365950751529 5020143221357524463063647)
  ·
    refine ⟨7530214832036286694595471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5020143221357524463063647 7530214832036286694595471)
    ·
      refine ⟨11295322248054430041893207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7530214832036286694595471 11295322248054430041893207)
      ·
        refine ⟨16942983372081645062839811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11295322248054430041893207 16942983372081645062839811)
        ·
          refine ⟨25414475058122467594259717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16942983372081645062839811 25414475058122467594259717)
          ·
            refine ⟨4765214073397962673923697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25414475058122467594259717 4765214073397962673923697)
            ·
              refine ⟨3573910555048472005442773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4765214073397962673923697 3573910555048472005442773)
              ·
                refine ⟨83763528633948562627565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3573910555048472005442773 83763528633948562627565)
                ·
                  rfl

theorem cell19_275280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_275280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275280 prefixEnd_275280 := by exact prefixLift 275280
  have htrace : WordTrace (prefixWord ++ tailWord_275280) baseStart_275280 baseEnd_275280 := by
    simpa [prefixWord, tailWord_275280, baseEnd_275280] using wordTrace_append hprefix tailTrace_275280
  have hstable : (prefixWord ++ tailWord_275280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275280).length < 2 ^ (prefixWord ++ tailWord_275280).sum := by decide
  have hdescent : baseEnd_275280 < baseStart_275280 := by decide
  rcases family_descends (prefixWord ++ tailWord_275280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275333 : List Nat := [1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_275333 : Nat := 118140960795 + 275333 * 2 ^ 59
def prefixEnd_275333 : Nat := 4983230072969 + 3 ^ 40 * 275333 * 2
def baseEnd_275333 : Nat := 83779655730060143449643

theorem tailTrace_275333 : CollatzResearch.WordTrace tailWord_275333 prefixEnd_275333 83779655730060143449643 := by
  unfold tailWord_275333
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042219511523038977806653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6694813007682025985204435 10042219511523038977806653)
  ·
    refine ⟨3765832316821139616677495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10042219511523038977806653 3765832316821139616677495)
    ·
      refine ⟨5648748475231709425016243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765832316821139616677495 5648748475231709425016243)
      ·
        refine ⟨8473122712847564137524365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648748475231709425016243 8473122712847564137524365)
        ·
          refine ⟨3177421017317836551571637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8473122712847564137524365 3177421017317836551571637)
          ·
            refine ⟨297883220373547176709841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3177421017317836551571637 297883220373547176709841)
            ·
              refine ⟨223412415280160382532381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297883220373547176709841 223412415280160382532381)
              ·
                refine ⟨83779655730060143449643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223412415280160382532381 83779655730060143449643)
                ·
                  rfl

theorem cell19_275333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_275333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275333 prefixEnd_275333 := by exact prefixLift 275333
  have htrace : WordTrace (prefixWord ++ tailWord_275333) baseStart_275333 baseEnd_275333 := by
    simpa [prefixWord, tailWord_275333, baseEnd_275333] using wordTrace_append hprefix tailTrace_275333
  have hstable : (prefixWord ++ tailWord_275333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275333).length < 2 ^ (prefixWord ++ tailWord_275333).sum := by decide
  have hdescent : baseEnd_275333 < baseStart_275333 := by decide
  rcases family_descends (prefixWord ++ tailWord_275333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275335 : List Nat := [1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_275335 : Nat := 118140960795 + 275335 * 2 ^ 59
def prefixEnd_275335 : Nat := 4983230072969 + 3 ^ 40 * 275335 * 2
def baseEnd_275335 : Nat := 83780264299724731405193

theorem tailTrace_275335 : CollatzResearch.WordTrace tailWord_275335 prefixEnd_275335 83780264299724731405193 := by
  unfold tailWord_275335
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042292457515793319379459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6694861638343862212919639 10042292457515793319379459)
  ·
    refine ⟨15063438686273689979069189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10042292457515793319379459 15063438686273689979069189)
    ·
      refine ⟨2824394753676316871075473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15063438686273689979069189 2824394753676316871075473)
      ·
        refine ⟨2118296065257237653306605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2824394753676316871075473 2118296065257237653306605)
        ·
          refine ⟨794361024471464119989977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2118296065257237653306605 794361024471464119989977)
          ·
            refine ⟨595770768353598089992483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794361024471464119989977 595770768353598089992483)
            ·
              refine ⟨893656152530397134988725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595770768353598089992483 893656152530397134988725)
              ·
                refine ⟨83780264299724731405193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 893656152530397134988725 83780264299724731405193)
                ·
                  rfl

theorem cell19_275335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_275335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275335 prefixEnd_275335 := by exact prefixLift 275335
  have htrace : WordTrace (prefixWord ++ tailWord_275335) baseStart_275335 baseEnd_275335 := by
    simpa [prefixWord, tailWord_275335, baseEnd_275335] using wordTrace_append hprefix tailTrace_275335
  have hstable : (prefixWord ++ tailWord_275335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275335).length < 2 ^ (prefixWord ++ tailWord_275335).sum := by decide
  have hdescent : baseEnd_275335 < baseStart_275335 := by decide
  rcases family_descends (prefixWord ++ tailWord_275335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275350 : List Nat := [5, 3, 1, 1, 1, 1, 7]
def baseStart_275350 : Nat := 118140960795 + 275350 * 2 ^ 59
def prefixEnd_275350 : Nat := 4983230072969 + 3 ^ 40 * 275350 * 2
def baseEnd_275350 : Nat := 27928276190736380357273

theorem tailTrace_275350 : CollatzResearch.WordTrace tailWord_275350 prefixEnd_275350 27928276190736380357273 := by
  unfold tailWord_275350
  simp only [CollatzResearch.WordTrace]
  refine ⟨627677472028840680073469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6695226368307633920783669 627677472028840680073469)
  ·
    refine ⟨235379052010815255027551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 627677472028840680073469 235379052010815255027551)
    ·
      refine ⟨353068578016222882541327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235379052010815255027551 353068578016222882541327)
      ·
        refine ⟨529602867024334323811991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353068578016222882541327 529602867024334323811991)
        ·
          refine ⟨794404300536501485717987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529602867024334323811991 794404300536501485717987)
          ·
            refine ⟨1191606450804752228576981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794404300536501485717987 1191606450804752228576981)
            ·
              refine ⟨27928276190736380357273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1191606450804752228576981 27928276190736380357273)
              ·
                rfl

theorem cell19_275350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_275350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275350 prefixEnd_275350 := by exact prefixLift 275350
  have htrace : WordTrace (prefixWord ++ tailWord_275350) baseStart_275350 baseEnd_275350 := by
    simpa [prefixWord, tailWord_275350, baseEnd_275350] using wordTrace_append hprefix tailTrace_275350
  have hstable : (prefixWord ++ tailWord_275350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275350).length < 2 ^ (prefixWord ++ tailWord_275350).sum := by decide
  have hdescent : baseEnd_275350 < baseStart_275350 := by decide
  rcases family_descends (prefixWord ++ tailWord_275350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275405 : List Nat := [1, 6, 3, 1, 2, 6]
def baseStart_275405 : Nat := 118140960795 + 275405 * 2 ^ 59
def prefixEnd_275405 : Nat := 4983230072969 + 3 ^ 40 * 275405 * 2
def baseEnd_275405 : Nat := 9311284915331701094383

theorem tailTrace_275405 : CollatzResearch.WordTrace tailWord_275405 prefixEnd_275405 9311284915331701094383 := by
  unfold tailWord_275405
  simp only [CollatzResearch.WordTrace]
  refine ⟨10044845567262195274427669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6696563711508130182951779 10044845567262195274427669)
  ·
    refine ⟨470852135965415403488797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10044845567262195274427669 470852135965415403488797)
    ·
      refine ⟨176569550987030776308299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 470852135965415403488797 176569550987030776308299)
      ·
        refine ⟨264854326480546164462449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176569550987030776308299 264854326480546164462449)
        ·
          refine ⟨198640744860409623346837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264854326480546164462449 198640744860409623346837)
          ·
            refine ⟨9311284915331701094383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 198640744860409623346837 9311284915331701094383)
            ·
              rfl

theorem cell19_275405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_275405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275405 prefixEnd_275405 := by exact prefixLift 275405
  have htrace : WordTrace (prefixWord ++ tailWord_275405) baseStart_275405 baseEnd_275405 := by
    simpa [prefixWord, tailWord_275405, baseEnd_275405] using wordTrace_append hprefix tailTrace_275405
  have hstable : (prefixWord ++ tailWord_275405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275405).length < 2 ^ (prefixWord ++ tailWord_275405).sum := by decide
  have hdescent : baseEnd_275405 < baseStart_275405 := by decide
  rcases family_descends (prefixWord ++ tailWord_275405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275413 : List Nat := [1, 3, 2, 3, 10]
def baseStart_275413 : Nat := 118140960795 + 275413 * 2 ^ 59
def prefixEnd_275413 : Nat := 4983230072969 + 3 ^ 40 * 275413 * 2
def baseEnd_275413 : Nat := 3103851796912728210061

theorem tailTrace_275413 : CollatzResearch.WordTrace tailWord_275413 prefixEnd_275413 3103851796912728210061 := by
  unfold tailWord_275413
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045137351233212640718893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6696758234155475093812595 10045137351233212640718893)
  ·
    refine ⟨3766926506712454740269585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10045137351233212640718893 3766926506712454740269585)
    ·
      refine ⟨2825194880034341055202189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3766926506712454740269585 2825194880034341055202189)
      ·
        refine ⟨1059448080012877895700821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2825194880034341055202189 1059448080012877895700821)
        ·
          refine ⟨3103851796912728210061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1059448080012877895700821 3103851796912728210061)
          ·
            rfl

theorem cell19_275413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 10].length) (baseStart_275413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275413 prefixEnd_275413 := by exact prefixLift 275413
  have htrace : WordTrace (prefixWord ++ tailWord_275413) baseStart_275413 baseEnd_275413 := by
    simpa [prefixWord, tailWord_275413, baseEnd_275413] using wordTrace_append hprefix tailTrace_275413
  have hstable : (prefixWord ++ tailWord_275413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275413).length < 2 ^ (prefixWord ++ tailWord_275413).sum := by decide
  have hdescent : baseEnd_275413 < baseStart_275413 := by decide
  rcases family_descends (prefixWord ++ tailWord_275413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275426 : List Nat := [3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_275426 : Nat := 118140960795 + 275426 * 2 ^ 59
def prefixEnd_275426 : Nat := 4983230072969 + 3 ^ 40 * 275426 * 2
def baseEnd_275426 : Nat := 83807954219463483382723

theorem tailTrace_275426 : CollatzResearch.WordTrace tailWord_275426 prefixEnd_275426 83807954219463483382723 := by
  unfold tailWord_275426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511402875046528965235533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6697074333457410573961421 2511402875046528965235533)
  ·
    refine ⟨941776078142448361963325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2511402875046528965235533 941776078142448361963325)
    ·
      refine ⟨353166029303418135736247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 941776078142448361963325 353166029303418135736247)
      ·
        refine ⟨529749043955127203604371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353166029303418135736247 529749043955127203604371)
        ·
          refine ⟨794623565932690805406557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529749043955127203604371 794623565932690805406557)
          ·
            refine ⟨297983837224759052027459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 794623565932690805406557 297983837224759052027459)
            ·
              refine ⟨446975755837138578041189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297983837224759052027459 446975755837138578041189)
              ·
                refine ⟨83807954219463483382723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446975755837138578041189 83807954219463483382723)
                ·
                  rfl

theorem cell19_275426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_275426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275426 prefixEnd_275426 := by exact prefixLift 275426
  have htrace : WordTrace (prefixWord ++ tailWord_275426) baseStart_275426 baseEnd_275426 := by
    simpa [prefixWord, tailWord_275426, baseEnd_275426] using wordTrace_append hprefix tailTrace_275426
  have hstable : (prefixWord ++ tailWord_275426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275426).length < 2 ^ (prefixWord ++ tailWord_275426).sum := by decide
  have hdescent : baseEnd_275426 < baseStart_275426 := by decide
  rcases family_descends (prefixWord ++ tailWord_275426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275449 : List Nat := [1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_275449 : Nat := 118140960795 + 275449 * 2 ^ 59
def prefixEnd_275449 : Nat := 4983230072969 + 3 ^ 40 * 275449 * 2
def baseEnd_275449 : Nat := 83814952770606244871549

theorem tailTrace_275449 : CollatzResearch.WordTrace tailWord_275449 prefixEnd_275449 83814952770606244871549 := by
  unfold tailWord_275449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046450379102790789029401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6697633586068527192686267 10046450379102790789029401)
  ·
    refine ⟨7534837784327093091772051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10046450379102790789029401 7534837784327093091772051)
    ·
      refine ⟨11302256676490639637658077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534837784327093091772051 11302256676490639637658077)
      ·
        refine ⟨4238346253683989864121779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11302256676490639637658077 4238346253683989864121779)
        ·
          refine ⟨6357519380525984796182669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238346253683989864121779 6357519380525984796182669)
          ·
            refine ⟨2384069767697244298568501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6357519380525984796182669 2384069767697244298568501)
            ·
              refine ⟨223506540721616652990797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2384069767697244298568501 223506540721616652990797)
              ·
                refine ⟨83814952770606244871549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223506540721616652990797 83814952770606244871549)
                ·
                  rfl

theorem cell19_275449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_275449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275449 prefixEnd_275449 := by exact prefixLift 275449
  have htrace : WordTrace (prefixWord ++ tailWord_275449) baseStart_275449 baseEnd_275449 := by
    simpa [prefixWord, tailWord_275449, baseEnd_275449] using wordTrace_append hprefix tailTrace_275449
  have hstable : (prefixWord ++ tailWord_275449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275449).length < 2 ^ (prefixWord ++ tailWord_275449).sum := by decide
  have hdescent : baseEnd_275449 < baseStart_275449 := by decide
  rcases family_descends (prefixWord ++ tailWord_275449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275527 : List Nat := [1, 1, 4, 1, 3, 2, 7]
def baseStart_275527 : Nat := 118140960795 + 275527 * 2 ^ 59
def prefixEnd_275527 : Nat := 4983230072969 + 3 ^ 40 * 275527 * 2
def baseEnd_275527 : Nat := 27946228995841725046001

theorem tailTrace_275527 : CollatzResearch.WordTrace tailWord_275527 prefixEnd_275527 27946228995841725046001 := by
  unfold tailWord_275527
  simp only [CollatzResearch.WordTrace]
  refine ⟨10049295272820210110368835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6699530181880140073579223 10049295272820210110368835)
  ·
    refine ⟨15073942909230315165553253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10049295272820210110368835 15073942909230315165553253)
    ·
      refine ⟨2826364295480684093541235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15073942909230315165553253 2826364295480684093541235)
      ·
        refine ⟨4239546443221026140311853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826364295480684093541235 4239546443221026140311853)
        ·
          refine ⟨1589829916207884802616945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4239546443221026140311853 1589829916207884802616945)
          ·
            refine ⟨1192372437155913601962709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589829916207884802616945 1192372437155913601962709)
            ·
              refine ⟨27946228995841725046001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1192372437155913601962709 27946228995841725046001)
              ·
                rfl

theorem cell19_275527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_275527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275527 prefixEnd_275527 := by exact prefixLift 275527
  have htrace : WordTrace (prefixWord ++ tailWord_275527) baseStart_275527 baseEnd_275527 := by
    simpa [prefixWord, tailWord_275527, baseEnd_275527] using wordTrace_append hprefix tailTrace_275527
  have hstable : (prefixWord ++ tailWord_275527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275527).length < 2 ^ (prefixWord ++ tailWord_275527).sum := by decide
  have hdescent : baseEnd_275527 < baseStart_275527 := by decide
  rcases family_descends (prefixWord ++ tailWord_275527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275603 : List Nat := [1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_275603 : Nat := 118140960795 + 275603 * 2 ^ 59
def prefixEnd_275603 : Nat := 4983230072969 + 3 ^ 40 * 275603 * 2
def baseEnd_275603 : Nat := 83861812634779517448907

theorem tailTrace_275603 : CollatzResearch.WordTrace tailWord_275603 prefixEnd_275603 83861812634779517448907 := by
  unfold tailWord_275603
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052067220544875090135463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6701378147029916726756975 10052067220544875090135463)
  ·
    refine ⟨15078100830817312635203195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10052067220544875090135463 15078100830817312635203195)
    ·
      refine ⟨22617151246225968952804793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15078100830817312635203195 22617151246225968952804793)
      ·
        refine ⟨16962863434669476714603595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22617151246225968952804793 16962863434669476714603595)
        ·
          refine ⟨25444295152004215071905393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16962863434669476714603595 25444295152004215071905393)
          ·
            refine ⟨19083221364003161303929045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25444295152004215071905393 19083221364003161303929045)
            ·
              refine ⟨447263000718824093060837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19083221364003161303929045 447263000718824093060837)
              ·
                refine ⟨83861812634779517448907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447263000718824093060837 83861812634779517448907)
                ·
                  rfl

theorem cell19_275603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_275603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275603 prefixEnd_275603 := by exact prefixLift 275603
  have htrace : WordTrace (prefixWord ++ tailWord_275603) baseStart_275603 baseEnd_275603 := by
    simpa [prefixWord, tailWord_275603, baseEnd_275603] using wordTrace_append hprefix tailTrace_275603
  have hstable : (prefixWord ++ tailWord_275603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275603).length < 2 ^ (prefixWord ++ tailWord_275603).sum := by decide
  have hdescent : baseEnd_275603 < baseStart_275603 := by decide
  rcases family_descends (prefixWord ++ tailWord_275603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275641 : List Nat := [1, 2, 1, 4, 1, 4, 6]
def baseStart_275641 : Nat := 118140960795 + 275641 * 2 ^ 59
def prefixEnd_275641 : Nat := 4983230072969 + 3 ^ 40 * 275641 * 2
def baseEnd_275641 : Nat := 27957791819468896201453

theorem tailTrace_275641 : CollatzResearch.WordTrace tailWord_275641 prefixEnd_275641 27957791819468896201453 := by
  unfold tailWord_275641
  simp only [CollatzResearch.WordTrace]
  refine ⟨10053453194407207580018777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6702302129604805053345851 10053453194407207580018777)
  ·
    refine ⟨7540089895805405685014083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10053453194407207580018777 7540089895805405685014083)
    ·
      refine ⟨11310134843708108527521125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7540089895805405685014083 11310134843708108527521125)
      ·
        refine ⟨2120650283195270348910211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11310134843708108527521125 2120650283195270348910211)
        ·
          refine ⟨3180975424792905523365317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120650283195270348910211 3180975424792905523365317)
          ·
            refine ⟨596432892148669785630997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3180975424792905523365317 596432892148669785630997)
            ·
              refine ⟨27957791819468896201453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 596432892148669785630997 27957791819468896201453)
              ·
                rfl

theorem cell19_275641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_275641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275641 prefixEnd_275641 := by exact prefixLift 275641
  have htrace : WordTrace (prefixWord ++ tailWord_275641) baseStart_275641 baseEnd_275641 := by
    simpa [prefixWord, tailWord_275641, baseEnd_275641] using wordTrace_append hprefix tailTrace_275641
  have hstable : (prefixWord ++ tailWord_275641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275641).length < 2 ^ (prefixWord ++ tailWord_275641).sum := by decide
  have hdescent : baseEnd_275641 < baseStart_275641 := by decide
  rcases family_descends (prefixWord ++ tailWord_275641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275717 : List Nat := [1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_275717 : Nat := 118140960795 + 275717 * 2 ^ 59
def prefixEnd_275717 : Nat := 4983230072969 + 3 ^ 40 * 275717 * 2
def baseEnd_275717 : Nat := 83896501105661030915263

theorem tailTrace_275717 : CollatzResearch.WordTrace tailWord_275717 prefixEnd_275717 83896501105661030915263 := by
  unfold tailWord_275717
  simp only [CollatzResearch.WordTrace]
  refine ⟨10056225142131872559785405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6704150094754581706523603 10056225142131872559785405)
  ·
    refine ⟨3771084428299452209919527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10056225142131872559785405 3771084428299452209919527)
    ·
      refine ⟨5656626642449178314879291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771084428299452209919527 5656626642449178314879291)
      ·
        refine ⟨8484939963673767472318937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5656626642449178314879291 8484939963673767472318937)
        ·
          refine ⟨6363704972755325604239203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8484939963673767472318937 6363704972755325604239203)
          ·
            refine ⟨9545557459132988406358805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363704972755325604239203 9545557459132988406358805)
            ·
              refine ⟨447448005896858831548069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9545557459132988406358805 447448005896858831548069)
              ·
                refine ⟨83896501105661030915263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447448005896858831548069 83896501105661030915263)
                ·
                  rfl

theorem cell19_275717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_275717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275717 prefixEnd_275717 := by exact prefixLift 275717
  have htrace : WordTrace (prefixWord ++ tailWord_275717) baseStart_275717 baseEnd_275717 := by
    simpa [prefixWord, tailWord_275717, baseEnd_275717] using wordTrace_append hprefix tailTrace_275717
  have hstable : (prefixWord ++ tailWord_275717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275717).length < 2 ^ (prefixWord ++ tailWord_275717).sum := by decide
  have hdescent : baseEnd_275717 < baseStart_275717 := by decide
  rcases family_descends (prefixWord ++ tailWord_275717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275736 : List Nat := [2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_275736 : Nat := 118140960795 + 275736 * 2 ^ 59
def prefixEnd_275736 : Nat := 4983230072969 + 3 ^ 40 * 275736 * 2
def baseEnd_275736 : Nat := 83902282517474616492989

theorem tailTrace_275736 : CollatzResearch.WordTrace tailWord_275736 prefixEnd_275736 83902282517474616492989 := by
  unfold tailWord_275736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028459064531519402363531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6704612086042025869818041 5028459064531519402363531)
  ·
    refine ⟨7542688596797279103545297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5028459064531519402363531 7542688596797279103545297)
    ·
      refine ⟨5657016447597959327658973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7542688596797279103545297 5657016447597959327658973)
      ·
        refine ⟨2121381167849234747872115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5657016447597959327658973 2121381167849234747872115)
        ·
          refine ⟨3182071751773852121808173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121381167849234747872115 3182071751773852121808173)
          ·
            refine ⟨1193276906915194545678065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3182071751773852121808173 1193276906915194545678065)
            ·
              refine ⟨894957680186395909258549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193276906915194545678065 894957680186395909258549)
              ·
                refine ⟨83902282517474616492989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 894957680186395909258549 83902282517474616492989)
                ·
                  rfl

theorem cell19_275736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_275736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275736 prefixEnd_275736 := by exact prefixLift 275736
  have htrace : WordTrace (prefixWord ++ tailWord_275736) baseStart_275736 baseEnd_275736 := by
    simpa [prefixWord, tailWord_275736, baseEnd_275736] using wordTrace_append hprefix tailTrace_275736
  have hstable : (prefixWord ++ tailWord_275736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275736).length < 2 ^ (prefixWord ++ tailWord_275736).sum := by decide
  have hdescent : baseEnd_275736 < baseStart_275736 := by decide
  rcases family_descends (prefixWord ++ tailWord_275736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275766 : List Nat := [5, 1, 2, 3, 2, 1, 1, 4]
def baseStart_275766 : Nat := 118140960795 + 275766 * 2 ^ 59
def prefixEnd_275766 : Nat := 4983230072969 + 3 ^ 40 * 275766 * 2
def baseEnd_275766 : Nat := 83911411062443435826241

theorem tailTrace_275766 : CollatzResearch.WordTrace tailWord_275766 prefixEnd_275766 83911411062443435826241 := by
  unfold tailWord_275766
  simp only [CollatzResearch.WordTrace]
  refine ⟨628625769934647120519947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6705341545969569285546101 628625769934647120519947)
  ·
    refine ⟨942938654901970680779921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 628625769934647120519947 942938654901970680779921)
    ·
      refine ⟨707203991176478010584941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 942938654901970680779921 707203991176478010584941)
      ·
        refine ⟨265201496691179253969353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 707203991176478010584941 265201496691179253969353)
        ·
          refine ⟨198901122518384440477015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265201496691179253969353 198901122518384440477015)
          ·
            refine ⟨298351683777576660715523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198901122518384440477015 298351683777576660715523)
            ·
              refine ⟨447527525666364991073285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298351683777576660715523 447527525666364991073285)
              ·
                refine ⟨83911411062443435826241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447527525666364991073285 83911411062443435826241)
                ·
                  rfl

theorem cell19_275766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_275766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275766 prefixEnd_275766 := by exact prefixLift 275766
  have htrace : WordTrace (prefixWord ++ tailWord_275766) baseStart_275766 baseEnd_275766 := by
    simpa [prefixWord, tailWord_275766, baseEnd_275766] using wordTrace_append hprefix tailTrace_275766
  have hstable : (prefixWord ++ tailWord_275766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275766).length < 2 ^ (prefixWord ++ tailWord_275766).sum := by decide
  have hdescent : baseEnd_275766 < baseStart_275766 := by decide
  rcases family_descends (prefixWord ++ tailWord_275766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275772 : List Nat := [2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_275772 : Nat := 118140960795 + 275772 * 2 ^ 59
def prefixEnd_275772 : Nat := 4983230072969 + 3 ^ 40 * 275772 * 2
def baseEnd_275772 : Nat := 83913236771437199692891

theorem tailTrace_275772 : CollatzResearch.WordTrace tailWord_275772 prefixEnd_275772 83913236771437199692891 := by
  unfold tailWord_275772
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029115578466308476518785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6705487437955077968691713 5029115578466308476518785)
  ·
    refine ⟨3771836683849731357389089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5029115578466308476518785 3771836683849731357389089)
    ·
      refine ⟨2828877512887298518041817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3771836683849731357389089 2828877512887298518041817)
      ·
        refine ⟨2121658134665473888531363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2828877512887298518041817 2121658134665473888531363)
        ·
          refine ⟨3182487201998210832797045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121658134665473888531363 3182487201998210832797045)
          ·
            refine ⟨298358175187332265574723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3182487201998210832797045 298358175187332265574723)
            ·
              refine ⟨447537262780998398362085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298358175187332265574723 447537262780998398362085)
              ·
                refine ⟨83913236771437199692891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447537262780998398362085 83913236771437199692891)
                ·
                  rfl

theorem cell19_275772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_275772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275772 prefixEnd_275772 := by exact prefixLift 275772
  have htrace : WordTrace (prefixWord ++ tailWord_275772) baseStart_275772 baseEnd_275772 := by
    simpa [prefixWord, tailWord_275772, baseEnd_275772] using wordTrace_append hprefix tailTrace_275772
  have hstable : (prefixWord ++ tailWord_275772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275772).length < 2 ^ (prefixWord ++ tailWord_275772).sum := by decide
  have hdescent : baseEnd_275772 < baseStart_275772 := by decide
  rcases family_descends (prefixWord ++ tailWord_275772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275812 : List Nat := [2, 3, 1, 1, 3, 3, 6]
def baseStart_275812 : Nat := 118140960795 + 275812 * 2 ^ 59
def prefixEnd_275812 : Nat := 4983230072969 + 3 ^ 40 * 275812 * 2
def baseEnd_275812 : Nat := 27975136054909652934631

theorem tailTrace_275812 : CollatzResearch.WordTrace tailWord_275812 prefixEnd_275812 27975136054909652934631 := by
  unfold tailWord_275812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029845038393851892246845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6706460051191802522995793 5029845038393851892246845)
  ·
    refine ⟨1886191889397694459592567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5029845038393851892246845 1886191889397694459592567)
    ·
      refine ⟨2829287834096541689388851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1886191889397694459592567 2829287834096541689388851)
      ·
        refine ⟨4243931751144812534083277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829287834096541689388851 4243931751144812534083277)
        ·
          refine ⟨1591474406679304700281229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4243931751144812534083277 1591474406679304700281229)
          ·
            refine ⟨596802902504739262605461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1591474406679304700281229 596802902504739262605461)
            ·
              refine ⟨27975136054909652934631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 596802902504739262605461 27975136054909652934631)
              ·
                rfl

theorem cell19_275812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_275812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275812 prefixEnd_275812 := by exact prefixLift 275812
  have htrace : WordTrace (prefixWord ++ tailWord_275812) baseStart_275812 baseEnd_275812 := by
    simpa [prefixWord, tailWord_275812, baseEnd_275812] using wordTrace_append hprefix tailTrace_275812
  have hstable : (prefixWord ++ tailWord_275812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275812).length < 2 ^ (prefixWord ++ tailWord_275812).sum := by decide
  have hdescent : baseEnd_275812 < baseStart_275812 := by decide
  rcases family_descends (prefixWord ++ tailWord_275812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275848 : List Nat := [2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_275848 : Nat := 118140960795 + 275848 * 2 ^ 59
def prefixEnd_275848 : Nat := 4983230072969 + 3 ^ 40 * 275848 * 2
def baseEnd_275848 : Nat := 83936362418691542003795

theorem tailTrace_275848 : CollatzResearch.WordTrace tailWord_275848 prefixEnd_275848 83936362418691542003795 := by
  unfold tailWord_275848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030501552328640966402099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6707335403104854621869465 5030501552328640966402099)
  ·
    refine ⟨7545752328492961449603149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5030501552328640966402099 7545752328492961449603149)
    ·
      refine ⟨2829657123184860543601181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7545752328492961449603149 2829657123184860543601181)
      ·
        refine ⟨1061121421194322703850443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2829657123184860543601181 1061121421194322703850443)
        ·
          refine ⟨1591682131791484055775665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061121421194322703850443 1591682131791484055775665)
          ·
            refine ⟨1193761598843613041831749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1591682131791484055775665 1193761598843613041831749)
            ·
              refine ⟨223830299783177445343453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1193761598843613041831749 223830299783177445343453)
              ·
                refine ⟨83936362418691542003795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223830299783177445343453 83936362418691542003795)
                ·
                  rfl

theorem cell19_275848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_275848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275848 prefixEnd_275848 := by exact prefixLift 275848
  have htrace : WordTrace (prefixWord ++ tailWord_275848) baseStart_275848 baseEnd_275848 := by
    simpa [prefixWord, tailWord_275848, baseEnd_275848] using wordTrace_append hprefix tailTrace_275848
  have hstable : (prefixWord ++ tailWord_275848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275848).length < 2 ^ (prefixWord ++ tailWord_275848).sum := by decide
  have hdescent : baseEnd_275848 < baseStart_275848 := by decide
  rcases family_descends (prefixWord ++ tailWord_275848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275869 : List Nat := [1, 4, 2, 1, 3, 1, 7]
def baseStart_275869 : Nat := 118140960795 + 275869 * 2 ^ 59
def prefixEnd_275869 : Nat := 4983230072969 + 3 ^ 40 * 275869 * 2
def baseEnd_275869 : Nat := 27980917466723238512357

theorem tailTrace_275869 : CollatzResearch.WordTrace tailWord_275869 prefixEnd_275869 27980917466723238512357 := by
  unfold tailWord_275869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061769037581202519318661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6707846025054135012879107 10061769037581202519318661)
  ·
    refine ⟨1886581694546475472372249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10061769037581202519318661 1886581694546475472372249)
    ·
      refine ⟨1414936270909856604279187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1886581694546475472372249 1414936270909856604279187)
      ·
        refine ⟨2122404406364784906418781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414936270909856604279187 2122404406364784906418781)
        ·
          refine ⟨795901652386794339907043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2122404406364784906418781 795901652386794339907043)
          ·
            refine ⟨1193852478580191509860565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795901652386794339907043 1193852478580191509860565)
            ·
              refine ⟨27980917466723238512357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1193852478580191509860565 27980917466723238512357)
              ·
                rfl

theorem cell19_275869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_275869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275869 prefixEnd_275869 := by exact prefixLift 275869
  have htrace : WordTrace (prefixWord ++ tailWord_275869) baseStart_275869 baseEnd_275869 := by
    simpa [prefixWord, tailWord_275869, baseEnd_275869] using wordTrace_append hprefix tailTrace_275869
  have hstable : (prefixWord ++ tailWord_275869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275869).length < 2 ^ (prefixWord ++ tailWord_275869).sum := by decide
  have hdescent : baseEnd_275869 < baseStart_275869 := by decide
  rcases family_descends (prefixWord ++ tailWord_275869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275924 : List Nat := [2, 4, 1, 2, 4, 6]
def baseStart_275924 : Nat := 118140960795 + 275924 * 2 ^ 59
def prefixEnd_275924 : Nat := 4983230072969 + 3 ^ 40 * 275924 * 2
def baseEnd_275924 : Nat := 9328832007327320479411

theorem tailTrace_275924 : CollatzResearch.WordTrace tailWord_275924 prefixEnd_275924 9328832007327320479411 := by
  unfold tailWord_275924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5031887526190973456285413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6709183368254631275047217 5031887526190973456285413)
  ·
    refine ⟨943478911160807523053515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5031887526190973456285413 943478911160807523053515)
    ·
      refine ⟨1415218366741211284580273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943478911160807523053515 1415218366741211284580273)
      ·
        refine ⟨1061413775055908463435205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1415218366741211284580273 1061413775055908463435205)
        ·
          refine ⟨199015082822982836894101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1061413775055908463435205 199015082822982836894101)
          ·
            refine ⟨9328832007327320479411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 199015082822982836894101 9328832007327320479411)
            ·
              rfl

theorem cell19_275924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_275924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275924 prefixEnd_275924 := by exact prefixLift 275924
  have htrace : WordTrace (prefixWord ++ tailWord_275924) baseStart_275924 baseEnd_275924 := by
    simpa [prefixWord, tailWord_275924, baseEnd_275924] using wordTrace_append hprefix tailTrace_275924
  have hstable : (prefixWord ++ tailWord_275924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275924).length < 2 ^ (prefixWord ++ tailWord_275924).sum := by decide
  have hdescent : baseEnd_275924 < baseStart_275924 := by decide
  rcases family_descends (prefixWord ++ tailWord_275924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275943 : List Nat := [1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_275943 : Nat := 118140960795 + 275943 * 2 ^ 59
def prefixEnd_275943 : Nat := 4983230072969 + 3 ^ 40 * 275943 * 2
def baseEnd_275943 : Nat := 83965269477759469892425

theorem tailTrace_275943 : CollatzResearch.WordTrace tailWord_275943 prefixEnd_275943 83965269477759469892425 := by
  unfold tailWord_275943
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064468039313113157512483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6709645359542075438341655 10064468039313113157512483)
  ·
    refine ⟨15096702058969669736268725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10064468039313113157512483 15096702058969669736268725)
    ·
      refine ⟨1415315818028406537775193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15096702058969669736268725 1415315818028406537775193)
      ·
        refine ⟨1061486863521304903331395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1415315818028406537775193 1061486863521304903331395)
        ·
          refine ⟨1592230295281957354997093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061486863521304903331395 1592230295281957354997093)
          ·
            refine ⟨298543180365367004061955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1592230295281957354997093 298543180365367004061955)
            ·
              refine ⟨447814770548050506092933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298543180365367004061955 447814770548050506092933)
              ·
                refine ⟨83965269477759469892425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447814770548050506092933 83965269477759469892425)
                ·
                  rfl

theorem cell19_275943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_275943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275943 prefixEnd_275943 := by exact prefixLift 275943
  have htrace : WordTrace (prefixWord ++ tailWord_275943) baseStart_275943 baseEnd_275943 := by
    simpa [prefixWord, tailWord_275943, baseEnd_275943] using wordTrace_append hprefix tailTrace_275943
  have hstable : (prefixWord ++ tailWord_275943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275943).length < 2 ^ (prefixWord ++ tailWord_275943).sum := by decide
  have hdescent : baseEnd_275943 < baseStart_275943 := by decide
  rcases family_descends (prefixWord ++ tailWord_275943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275947 : List Nat := [1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_275947 : Nat := 118140960795 + 275947 * 2 ^ 59
def prefixEnd_275947 : Nat := 4983230072969 + 3 ^ 40 * 275947 * 2
def baseEnd_275947 : Nat := 83966486617088645803525

theorem tailTrace_275947 : CollatzResearch.WordTrace tailWord_275947 prefixEnd_275947 83966486617088645803525 := by
  unfold tailWord_275947
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064613931298621840658095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6709742620865747893772063 10064613931298621840658095)
  ·
    refine ⟨15096920896947932760987143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10064613931298621840658095 15096920896947932760987143)
    ·
      refine ⟨22645381345421899141480715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15096920896947932760987143 22645381345421899141480715)
      ·
        refine ⟨33968072018132848712221073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22645381345421899141480715 33968072018132848712221073)
        ·
          refine ⟨25476054013599636534165805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33968072018132848712221073 25476054013599636534165805)
          ·
            refine ⟨9553520255099863700312177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25476054013599636534165805 9553520255099863700312177)
            ·
              refine ⟨7165140191324897775234133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9553520255099863700312177 7165140191324897775234133)
              ·
                refine ⟨83966486617088645803525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7165140191324897775234133 83966486617088645803525)
                ·
                  rfl

theorem cell19_275947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_275947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275947 prefixEnd_275947 := by exact prefixLift 275947
  have htrace : WordTrace (prefixWord ++ tailWord_275947) baseStart_275947 baseEnd_275947 := by
    simpa [prefixWord, tailWord_275947, baseEnd_275947] using wordTrace_append hprefix tailTrace_275947
  have hstable : (prefixWord ++ tailWord_275947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275947).length < 2 ^ (prefixWord ++ tailWord_275947).sum := by decide
  have hdescent : baseEnd_275947 < baseStart_275947 := by decide
  rcases family_descends (prefixWord ++ tailWord_275947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275985 : List Nat := [1, 2, 2, 1, 1, 2, 10]
def baseStart_275985 : Nat := 118140960795 + 275985 * 2 ^ 59
def prefixEnd_275985 : Nat := 4983230072969 + 3 ^ 40 * 275985 * 2
def baseEnd_275985 : Nat := 27992683146905272319659

theorem tailTrace_275985 : CollatzResearch.WordTrace tailWord_275985 prefixEnd_275985 27992683146905272319659 := by
  unfold tailWord_275985
  simp only [CollatzResearch.WordTrace]
  refine ⟨10065999905160954330541409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6710666603440636220360939 10065999905160954330541409)
  ·
    refine ⟨7549499928870715747906057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10065999905160954330541409 7549499928870715747906057)
    ·
      refine ⟨5662124946653036810929543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7549499928870715747906057 5662124946653036810929543)
      ·
        refine ⟨8493187419979555216394315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5662124946653036810929543 8493187419979555216394315)
        ·
          refine ⟨12739781129969332824591473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8493187419979555216394315 12739781129969332824591473)
          ·
            refine ⟨9554835847476999618443605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12739781129969332824591473 9554835847476999618443605)
            ·
              refine ⟨27992683146905272319659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9554835847476999618443605 27992683146905272319659)
              ·
                rfl

theorem cell19_275985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_275985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_275985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_275985 prefixEnd_275985 := by exact prefixLift 275985
  have htrace : WordTrace (prefixWord ++ tailWord_275985) baseStart_275985 baseEnd_275985 := by
    simpa [prefixWord, tailWord_275985, baseEnd_275985] using wordTrace_append hprefix tailTrace_275985
  have hstable : (prefixWord ++ tailWord_275985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275985).length < 2 ^ (prefixWord ++ tailWord_275985).sum := by decide
  have hdescent : baseEnd_275985 < baseStart_275985 := by decide
  rcases family_descends (prefixWord ++ tailWord_275985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276019 : List Nat := [1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_276019 : Nat := 118140960795 + 276019 * 2 ^ 59
def prefixEnd_276019 : Nat := 4983230072969 + 3 ^ 40 * 276019 * 2
def baseEnd_276019 : Nat := 83988395125013812203329

theorem tailTrace_276019 : CollatzResearch.WordTrace tailWord_276019 prefixEnd_276019 83988395125013812203329 := by
  unfold tailWord_276019
  simp only [CollatzResearch.WordTrace]
  refine ⟨10067239987037778137279111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6711493324691852091519407 10067239987037778137279111)
  ·
    refine ⟨15100859980556667205918667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10067239987037778137279111 15100859980556667205918667)
    ·
      refine ⟨22651289970835000808878001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15100859980556667205918667 22651289970835000808878001)
      ·
        refine ⟨16988467478126250606658501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22651289970835000808878001 16988467478126250606658501)
        ·
          refine ⟨3185337652148671988748469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16988467478126250606658501 3185337652148671988748469)
          ·
            refine ⟨298625404888937998945169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3185337652148671988748469 298625404888937998945169)
            ·
              refine ⟨223969053666703499208877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298625404888937998945169 223969053666703499208877)
              ·
                refine ⟨83988395125013812203329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223969053666703499208877 83988395125013812203329)
                ·
                  rfl

theorem cell19_276019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_276019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276019 prefixEnd_276019 := by exact prefixLift 276019
  have htrace : WordTrace (prefixWord ++ tailWord_276019) baseStart_276019 baseEnd_276019 := by
    simpa [prefixWord, tailWord_276019, baseEnd_276019] using wordTrace_append hprefix tailTrace_276019
  have hstable : (prefixWord ++ tailWord_276019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276019).length < 2 ^ (prefixWord ++ tailWord_276019).sum := by decide
  have hdescent : baseEnd_276019 < baseStart_276019 := by decide
  rcases family_descends (prefixWord ++ tailWord_276019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276021 : List Nat := [1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_276021 : Nat := 118140960795 + 276021 * 2 ^ 59
def prefixEnd_276021 : Nat := 4983230072969 + 3 ^ 40 * 276021 * 2
def baseEnd_276021 : Nat := 83989003694678400158879

theorem tailTrace_276021 : CollatzResearch.WordTrace tailWord_276021 prefixEnd_276021 83989003694678400158879 := by
  unfold tailWord_276021
  simp only [CollatzResearch.WordTrace]
  refine ⟨10067312933030532478851917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6711541955353688319234611 10067312933030532478851917)
  ·
    refine ⟨3775242349886449679569469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10067312933030532478851917 3775242349886449679569469)
    ·
      refine ⟨1415715881207418629838551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3775242349886449679569469 1415715881207418629838551)
      ·
        refine ⟨2123573821811127944757827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415715881207418629838551 2123573821811127944757827)
        ·
          refine ⟨3185360732716691917136741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123573821811127944757827 3185360732716691917136741)
          ·
            refine ⟨597255137384379734463139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3185360732716691917136741 597255137384379734463139)
            ·
              refine ⟨895882706076569601694709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597255137384379734463139 895882706076569601694709)
              ·
                refine ⟨83989003694678400158879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 895882706076569601694709 83989003694678400158879)
                ·
                  rfl

theorem cell19_276021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_276021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276021 prefixEnd_276021 := by exact prefixLift 276021
  have htrace : WordTrace (prefixWord ++ tailWord_276021) baseStart_276021 baseEnd_276021 := by
    simpa [prefixWord, tailWord_276021, baseEnd_276021] using wordTrace_append hprefix tailTrace_276021
  have hstable : (prefixWord ++ tailWord_276021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276021).length < 2 ^ (prefixWord ++ tailWord_276021).sum := by decide
  have hdescent : baseEnd_276021 < baseStart_276021 := by decide
  rcases family_descends (prefixWord ++ tailWord_276021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276192 : List Nat := [2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_276192 : Nat := 118140960795 + 276192 * 2 ^ 59
def prefixEnd_276192 : Nat := 4983230072969 + 3 ^ 40 * 276192 * 2
def baseEnd_276192 : Nat := 84041036401000670358413

theorem tailTrace_276192 : CollatzResearch.WordTrace tailWord_276192 prefixEnd_276192 84041036401000670358413 := by
  unfold tailWord_276192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036774907705514341663415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6715699876940685788884553 5036774907705514341663415)
  ·
    refine ⟨7555162361558271512495123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036774907705514341663415 7555162361558271512495123)
    ·
      refine ⟨11332743542337407268742685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7555162361558271512495123 11332743542337407268742685)
      ·
        refine ⟨4249778828376527725778507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11332743542337407268742685 4249778828376527725778507)
        ·
          refine ⟨6374668242564791588667761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249778828376527725778507 6374668242564791588667761)
          ·
            refine ⟨4781001181923593691500821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6374668242564791588667761 4781001181923593691500821)
            ·
              refine ⟨224109430402668454289101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4781001181923593691500821 224109430402668454289101)
              ·
                refine ⟨84041036401000670358413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224109430402668454289101 84041036401000670358413)
                ·
                  rfl

theorem cell19_276192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_276192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276192 prefixEnd_276192 := by exact prefixLift 276192
  have htrace : WordTrace (prefixWord ++ tailWord_276192) baseStart_276192 baseEnd_276192 := by
    simpa [prefixWord, tailWord_276192, baseEnd_276192] using wordTrace_append hprefix tailTrace_276192
  have hstable : (prefixWord ++ tailWord_276192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276192).length < 2 ^ (prefixWord ++ tailWord_276192).sum := by decide
  have hdescent : baseEnd_276192 < baseStart_276192 := by decide
  rcases family_descends (prefixWord ++ tailWord_276192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276285 : List Nat := [1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_276285 : Nat := 118140960795 + 276285 * 2 ^ 59
def prefixEnd_276285 : Nat := 4983230072969 + 3 ^ 40 * 276285 * 2
def baseEnd_276285 : Nat := 84069334890404010291493

theorem tailTrace_276285 : CollatzResearch.WordTrace tailWord_276285 prefixEnd_276285 84069334890404010291493 := by
  unfold tailWord_276285
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076941804074105566462309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6717961202716070377641539 10076941804074105566462309)
  ·
    refine ⟨1889426588263894793711683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10076941804074105566462309 1889426588263894793711683)
    ·
      refine ⟨2834139882395842190567525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1889426588263894793711683 2834139882395842190567525)
      ·
        refine ⟨531401227949220410731411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2834139882395842190567525 531401227949220410731411)
        ·
          refine ⟨797101841923830616097117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531401227949220410731411 797101841923830616097117)
          ·
            refine ⟨298913190721436481036419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 797101841923830616097117 298913190721436481036419)
            ·
              refine ⟨448369786082154721554629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298913190721436481036419 448369786082154721554629)
              ·
                refine ⟨84069334890404010291493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448369786082154721554629 84069334890404010291493)
                ·
                  rfl

theorem cell19_276285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_276285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276285 prefixEnd_276285 := by exact prefixLift 276285
  have htrace : WordTrace (prefixWord ++ tailWord_276285) baseStart_276285 baseEnd_276285 := by
    simpa [prefixWord, tailWord_276285, baseEnd_276285] using wordTrace_append hprefix tailTrace_276285
  have hstable : (prefixWord ++ tailWord_276285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276285).length < 2 ^ (prefixWord ++ tailWord_276285).sum := by decide
  have hdescent : baseEnd_276285 < baseStart_276285 := by decide
  rcases family_descends (prefixWord ++ tailWord_276285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276327 : List Nat := [1, 1, 5, 1, 2, 1, 8]
def baseStart_276327 : Nat := 118140960795 + 276327 * 2 ^ 59
def prefixEnd_276327 : Nat := 4983230072969 + 3 ^ 40 * 276327 * 2
def baseEnd_276327 : Nat := 28027371617786785786015

theorem tailTrace_276327 : CollatzResearch.WordTrace tailWord_276327 prefixEnd_276327 28027371617786785786015 := by
  unfold tailWord_276327
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078473669921946739491235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6718982446614631159660823 10078473669921946739491235)
  ·
    refine ⟨15117710504882920109236853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10078473669921946739491235 15117710504882920109236853)
    ·
      refine ⟨1417285359832773760240955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15117710504882920109236853 1417285359832773760240955)
      ·
        refine ⟨2125928039749160640361433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417285359832773760240955 2125928039749160640361433)
        ·
          refine ⟨1594446029811870480271075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125928039749160640361433 1594446029811870480271075)
          ·
            refine ⟨2391669044717805720406613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594446029811870480271075 2391669044717805720406613)
            ·
              refine ⟨28027371617786785786015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2391669044717805720406613 28027371617786785786015)
              ·
                rfl

theorem cell19_276327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_276327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276327 prefixEnd_276327 := by exact prefixLift 276327
  have htrace : WordTrace (prefixWord ++ tailWord_276327) baseStart_276327 baseEnd_276327 := by
    simpa [prefixWord, tailWord_276327, baseEnd_276327] using wordTrace_append hprefix tailTrace_276327
  have hstable : (prefixWord ++ tailWord_276327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276327).length < 2 ^ (prefixWord ++ tailWord_276327).sum := by decide
  have hdescent : baseEnd_276327 < baseStart_276327 := by decide
  rcases family_descends (prefixWord ++ tailWord_276327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276359 : List Nat := [1, 1, 4, 2, 5, 1, 2, 3]
def baseStart_276359 : Nat := 118140960795 + 276359 * 2 ^ 59
def prefixEnd_276359 : Nat := 4983230072969 + 3 ^ 40 * 276359 * 2
def baseEnd_276359 : Nat := 84091851967993764646847

theorem tailTrace_276359 : CollatzResearch.WordTrace tailWord_276359 prefixEnd_276359 84091851967993764646847 := by
  unfold tailWord_276359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079640805806016204656131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6719760537204010803104087 10079640805806016204656131)
  ·
    refine ⟨15119461208709024306984197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10079640805806016204656131 15119461208709024306984197)
    ·
      refine ⟨2834898976632942057559537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15119461208709024306984197 2834898976632942057559537)
      ·
        refine ⟨2126174232474706543169653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2834898976632942057559537 2126174232474706543169653)
        ·
          refine ⟨199328834294503738422155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2126174232474706543169653 199328834294503738422155)
          ·
            refine ⟨298993251441755607633233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199328834294503738422155 298993251441755607633233)
            ·
              refine ⟨224244938581316705724925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298993251441755607633233 224244938581316705724925)
              ·
                refine ⟨84091851967993764646847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224244938581316705724925 84091851967993764646847)
                ·
                  rfl

theorem cell19_276359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_276359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276359 prefixEnd_276359 := by exact prefixLift 276359
  have htrace : WordTrace (prefixWord ++ tailWord_276359) baseStart_276359 baseEnd_276359 := by
    simpa [prefixWord, tailWord_276359, baseEnd_276359] using wordTrace_append hprefix tailTrace_276359
  have hstable : (prefixWord ++ tailWord_276359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276359).length < 2 ^ (prefixWord ++ tailWord_276359).sum := by decide
  have hdescent : baseEnd_276359 < baseStart_276359 := by decide
  rcases family_descends (prefixWord ++ tailWord_276359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276401 : List Nat := [1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_276401 : Nat := 118140960795 + 276401 * 2 ^ 59
def prefixEnd_276401 : Nat := 4983230072969 + 3 ^ 40 * 276401 * 2
def baseEnd_276401 : Nat := 84104631930950111713399

theorem tailTrace_276401 : CollatzResearch.WordTrace tailWord_276401 prefixEnd_276401 84104631930950111713399 := by
  unfold tailWord_276401
  simp only [CollatzResearch.WordTrace]
  refine ⟨10081172671653857377685057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6720781781102571585123371 10081172671653857377685057)
  ·
    refine ⟨7560879503740393033263793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10081172671653857377685057 7560879503740393033263793)
    ·
      refine ⟨5670659627805294774947845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7560879503740393033263793 5670659627805294774947845)
      ·
        refine ⟨1063248680213492770302721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5670659627805294774947845 1063248680213492770302721)
        ·
          refine ⟨797436510160119577727041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063248680213492770302721 797436510160119577727041)
          ·
            refine ⟨598077382620089683295281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797436510160119577727041 598077382620089683295281)
            ·
              refine ⟨448558036965067262471461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598077382620089683295281 448558036965067262471461)
              ·
                refine ⟨84104631930950111713399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448558036965067262471461 84104631930950111713399)
                ·
                  rfl

theorem cell19_276401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_276401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276401 prefixEnd_276401 := by exact prefixLift 276401
  have htrace : WordTrace (prefixWord ++ tailWord_276401) baseStart_276401 baseEnd_276401 := by
    simpa [prefixWord, tailWord_276401, baseEnd_276401] using wordTrace_append hprefix tailTrace_276401
  have hstable : (prefixWord ++ tailWord_276401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276401).length < 2 ^ (prefixWord ++ tailWord_276401).sum := by decide
  have hdescent : baseEnd_276401 < baseStart_276401 := by decide
  rcases family_descends (prefixWord ++ tailWord_276401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276403 : List Nat := [1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_276403 : Nat := 118140960795 + 276403 * 2 ^ 59
def prefixEnd_276403 : Nat := 4983230072969 + 3 ^ 40 * 276403 * 2
def baseEnd_276403 : Nat := 84105240500614699668949

theorem tailTrace_276403 : CollatzResearch.WordTrace tailWord_276403 prefixEnd_276403 84105240500614699668949 := by
  unfold tailWord_276403
  simp only [CollatzResearch.WordTrace]
  refine ⟨10081245617646611719257863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6720830411764407812838575 10081245617646611719257863)
  ·
    refine ⟨15121868426469917578886795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10081245617646611719257863 15121868426469917578886795)
    ·
      refine ⟨22682802639704876368330193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15121868426469917578886795 22682802639704876368330193)
      ·
        refine ⟨17012101979778657276247645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22682802639704876368330193 17012101979778657276247645)
        ·
          refine ⟨6379538242416996478592867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17012101979778657276247645 6379538242416996478592867)
          ·
            refine ⟨9569307363625494717889301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6379538242416996478592867 9569307363625494717889301)
            ·
              refine ⟨448561282669945064901061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9569307363625494717889301 448561282669945064901061)
              ·
                refine ⟨84105240500614699668949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448561282669945064901061 84105240500614699668949)
                ·
                  rfl

theorem cell19_276403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_276403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276403 prefixEnd_276403 := by exact prefixLift 276403
  have htrace : WordTrace (prefixWord ++ tailWord_276403) baseStart_276403 baseEnd_276403 := by
    simpa [prefixWord, tailWord_276403, baseEnd_276403] using wordTrace_append hprefix tailTrace_276403
  have hstable : (prefixWord ++ tailWord_276403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276403).length < 2 ^ (prefixWord ++ tailWord_276403).sum := by decide
  have hdescent : baseEnd_276403 < baseStart_276403 := by decide
  rcases family_descends (prefixWord ++ tailWord_276403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276441 : List Nat := [1, 2, 1, 2, 6, 7]
def baseStart_276441 : Nat := 118140960795 + 276441 * 2 ^ 59
def prefixEnd_276441 : Nat := 4983230072969 + 3 ^ 40 * 276441 * 2
def baseEnd_276441 : Nat := 9346311480471318980489

theorem tailTrace_276441 : CollatzResearch.WordTrace tailWord_276441 prefixEnd_276441 9346311480471318980489 := by
  unfold tailWord_276441
  simp only [CollatzResearch.WordTrace]
  refine ⟨10082631591508944209141177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6721754394339296139427451 10082631591508944209141177)
  ·
    refine ⟨7561973693631708156855883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10082631591508944209141177 7561973693631708156855883)
    ·
      refine ⟨11342960540447562235283825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7561973693631708156855883 11342960540447562235283825)
      ·
        refine ⟨8507220405335671676462869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11342960540447562235283825 8507220405335671676462869)
        ·
          refine ⟨398775956500109609834197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8507220405335671676462869 398775956500109609834197)
          ·
            refine ⟨9346311480471318980489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 398775956500109609834197 9346311480471318980489)
            ·
              rfl

theorem cell19_276441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_276441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276441 prefixEnd_276441 := by exact prefixLift 276441
  have htrace : WordTrace (prefixWord ++ tailWord_276441) baseStart_276441 baseEnd_276441 := by
    simpa [prefixWord, tailWord_276441, baseEnd_276441] using wordTrace_append hprefix tailTrace_276441
  have hstable : (prefixWord ++ tailWord_276441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276441).length < 2 ^ (prefixWord ++ tailWord_276441).sum := by decide
  have hdescent : baseEnd_276441 < baseStart_276441 := by decide
  rcases family_descends (prefixWord ++ tailWord_276441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276532 : List Nat := [2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_276532 : Nat := 118140960795 + 276532 * 2 ^ 59
def prefixEnd_276532 : Nat := 4983230072969 + 3 ^ 40 * 276532 * 2
def baseEnd_276532 : Nat := 84144493243980622801931

theorem tailTrace_276532 : CollatzResearch.WordTrace tailWord_276532 prefixEnd_276532 84144493243980622801931 := by
  unfold tailWord_276532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042975317089633375351925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6723967089452844500469233 5042975317089633375351925)
  ·
    refine ⟨472778935977153128939243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5042975317089633375351925 472778935977153128939243)
    ·
      refine ⟨709168403965729693408865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472778935977153128939243 709168403965729693408865)
      ·
        refine ⟨531876302974297270056649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 709168403965729693408865 531876302974297270056649)
        ·
          refine ⟨398907227230722952542487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531876302974297270056649 398907227230722952542487)
          ·
            refine ⟨598360840846084428813731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398907227230722952542487 598360840846084428813731)
            ·
              refine ⟨897541261269126643220597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598360840846084428813731 897541261269126643220597)
              ·
                refine ⟨84144493243980622801931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897541261269126643220597 84144493243980622801931)
                ·
                  rfl

theorem cell19_276532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_276532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276532 prefixEnd_276532 := by exact prefixLift 276532
  have htrace : WordTrace (prefixWord ++ tailWord_276532) baseStart_276532 baseEnd_276532 := by
    simpa [prefixWord, tailWord_276532, baseEnd_276532] using wordTrace_append hprefix tailTrace_276532
  have hstable : (prefixWord ++ tailWord_276532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276532).length < 2 ^ (prefixWord ++ tailWord_276532).sum := by decide
  have hdescent : baseEnd_276532 < baseStart_276532 := by decide
  rcases family_descends (prefixWord ++ tailWord_276532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276534 : List Nat := [5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_276534 : Nat := 118140960795 + 276534 * 2 ^ 59
def prefixEnd_276534 : Nat := 4983230072969 + 3 ^ 40 * 276534 * 2
def baseEnd_276534 : Nat := 84145101813645210757481

theorem tailTrace_276534 : CollatzResearch.WordTrace tailWord_276534 prefixEnd_276534 84145101813645210757481 := by
  unfold tailWord_276534
  simp only [CollatzResearch.WordTrace]
  refine ⟨630376473760751318267291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6724015720114680728184437 630376473760751318267291)
  ·
    refine ⟨945564710641126977400937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630376473760751318267291 945564710641126977400937)
    ·
      refine ⟨709173532980845233050703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945564710641126977400937 709173532980845233050703)
      ·
        refine ⟨1063760299471267849576055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709173532980845233050703 1063760299471267849576055)
        ·
          refine ⟨1595640449206901774364083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063760299471267849576055 1595640449206901774364083)
          ·
            refine ⟨2393460673810352661546125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595640449206901774364083 2393460673810352661546125)
            ·
              refine ⟨897547752678882248079797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2393460673810352661546125 897547752678882248079797)
              ·
                refine ⟨84145101813645210757481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897547752678882248079797 84145101813645210757481)
                ·
                  rfl

theorem cell19_276534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_276534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276534 prefixEnd_276534 := by exact prefixLift 276534
  have htrace : WordTrace (prefixWord ++ tailWord_276534) baseStart_276534 baseEnd_276534 := by
    simpa [prefixWord, tailWord_276534, baseEnd_276534] using wordTrace_append hprefix tailTrace_276534
  have hstable : (prefixWord ++ tailWord_276534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276534).length < 2 ^ (prefixWord ++ tailWord_276534).sum := by decide
  have hdescent : baseEnd_276534 < baseStart_276534 := by decide
  rcases family_descends (prefixWord ++ tailWord_276534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276572 : List Nat := [2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_276572 : Nat := 118140960795 + 276572 * 2 ^ 59
def prefixEnd_276572 : Nat := 4983230072969 + 3 ^ 40 * 276572 * 2
def baseEnd_276572 : Nat := 84156664637272381912933

theorem tailTrace_276572 : CollatzResearch.WordTrace tailWord_276572 prefixEnd_276572 84156664637272381912933 := by
  unfold tailWord_276572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043704777017176791079985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6724939702689569054773313 5043704777017176791079985)
  ·
    refine ⟨3782778582762882593309989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5043704777017176791079985 3782778582762882593309989)
    ·
      refine ⟨709270984268040486245623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3782778582762882593309989 709270984268040486245623)
      ·
        refine ⟨1063906476402060729368435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709270984268040486245623 1063906476402060729368435)
        ·
          refine ⟨1595859714603091094052653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063906476402060729368435 1595859714603091094052653)
          ·
            refine ⟨598447392976159160269745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1595859714603091094052653 598447392976159160269745)
            ·
              refine ⟨448835544732119370202309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598447392976159160269745 448835544732119370202309)
              ·
                refine ⟨84156664637272381912933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448835544732119370202309 84156664637272381912933)
                ·
                  rfl

theorem cell19_276572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_276572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276572 prefixEnd_276572 := by exact prefixLift 276572
  have htrace : WordTrace (prefixWord ++ tailWord_276572) baseStart_276572 baseEnd_276572 := by
    simpa [prefixWord, tailWord_276572, baseEnd_276572] using wordTrace_append hprefix tailTrace_276572
  have hstable : (prefixWord ++ tailWord_276572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276572).length < 2 ^ (prefixWord ++ tailWord_276572).sum := by decide
  have hdescent : baseEnd_276572 < baseStart_276572 := by decide
  rcases family_descends (prefixWord ++ tailWord_276572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276726 : List Nat := [5, 1, 1, 1, 1, 1, 9]
def baseStart_276726 : Nat := 118140960795 + 276726 * 2 ^ 59
def prefixEnd_276726 : Nat := 4983230072969 + 3 ^ 40 * 276726 * 2
def baseEnd_276726 : Nat := 28067841500481884830097

theorem tailTrace_276726 : CollatzResearch.WordTrace tailWord_276726 prefixEnd_276726 28067841500481884830097 := by
  unfold tailWord_276726
  simp only [CollatzResearch.WordTrace]
  refine ⟨630814149717277367704127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6728684263650958588844021 630814149717277367704127)
  ·
    refine ⟨946221224575916051556191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630814149717277367704127 946221224575916051556191)
    ·
      refine ⟨1419331836863874077334287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946221224575916051556191 1419331836863874077334287)
      ·
        refine ⟨2128997755295811116001431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419331836863874077334287 2128997755295811116001431)
        ·
          refine ⟨3193496632943716674002147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128997755295811116001431 3193496632943716674002147)
          ·
            refine ⟨4790244949415575011003221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193496632943716674002147 4790244949415575011003221)
            ·
              refine ⟨28067841500481884830097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4790244949415575011003221 28067841500481884830097)
              ·
                rfl

theorem cell19_276726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_276726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276726 prefixEnd_276726 := by exact prefixLift 276726
  have htrace : WordTrace (prefixWord ++ tailWord_276726) baseStart_276726 baseEnd_276726 := by
    simpa [prefixWord, tailWord_276726, baseEnd_276726] using wordTrace_append hprefix tailTrace_276726
  have hstable : (prefixWord ++ tailWord_276726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276726).length < 2 ^ (prefixWord ++ tailWord_276726).sum := by decide
  have hdescent : baseEnd_276726 < baseStart_276726 := by decide
  rcases family_descends (prefixWord ++ tailWord_276726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276745 : List Nat := [1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_276745 : Nat := 118140960795 + 276745 * 2 ^ 59
def prefixEnd_276745 : Nat := 4983230072969 + 3 ^ 40 * 276745 * 2
def baseEnd_276745 : Nat := 84209305913259240068017

theorem tailTrace_276745 : CollatzResearch.WordTrace tailWord_276745 prefixEnd_276745 84209305913259240068017 := by
  unfold tailWord_276745
  simp only [CollatzResearch.WordTrace]
  refine ⟨10093719382407604128207689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6729146254938402752138459 10093719382407604128207689)
  ·
    refine ⟨7570289536805703096155767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10093719382407604128207689 7570289536805703096155767)
    ·
      refine ⟨11355434305208554644233651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7570289536805703096155767 11355434305208554644233651)
      ·
        refine ⟨17033151457812831966350477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355434305208554644233651 17033151457812831966350477)
        ·
          refine ⟨6387431796679811987381429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17033151457812831966350477 6387431796679811987381429)
          ·
            refine ⟨598821730938732373817009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6387431796679811987381429 598821730938732373817009)
            ·
              refine ⟨449116298204049280362757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598821730938732373817009 449116298204049280362757)
              ·
                refine ⟨84209305913259240068017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 449116298204049280362757 84209305913259240068017)
                ·
                  rfl

theorem cell19_276745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_276745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276745 prefixEnd_276745 := by exact prefixLift 276745
  have htrace : WordTrace (prefixWord ++ tailWord_276745) baseStart_276745 baseEnd_276745 := by
    simpa [prefixWord, tailWord_276745, baseEnd_276745] using wordTrace_append hprefix tailTrace_276745
  have hstable : (prefixWord ++ tailWord_276745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276745).length < 2 ^ (prefixWord ++ tailWord_276745).sum := by decide
  have hdescent : baseEnd_276745 < baseStart_276745 := by decide
  rcases family_descends (prefixWord ++ tailWord_276745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276781 : List Nat := [1, 5, 3, 1, 2, 7]
def baseStart_276781 : Nat := 118140960795 + 276781 * 2 ^ 59
def prefixEnd_276781 : Nat := 4983230072969 + 3 ^ 40 * 276781 * 2
def baseEnd_276781 : Nat := 9357806685246869251991

theorem tailTrace_276781 : CollatzResearch.WordTrace tailWord_276781 prefixEnd_276781 9357806685246869251991 := by
  unfold tailWord_276781
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095032410277182276518197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6730021606851454851012131 10095032410277182276518197)
  ·
    refine ⟨946409288463485838423581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10095032410277182276518197 946409288463485838423581)
    ·
      refine ⟨354903483173807189408843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 946409288463485838423581 354903483173807189408843)
      ·
        refine ⟨532355224760710784113265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354903483173807189408843 532355224760710784113265)
        ·
          refine ⟨399266418570533088084949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532355224760710784113265 399266418570533088084949)
          ·
            refine ⟨9357806685246869251991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 399266418570533088084949 9357806685246869251991)
            ·
              rfl

theorem cell19_276781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_276781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276781 prefixEnd_276781 := by exact prefixLift 276781
  have htrace : WordTrace (prefixWord ++ tailWord_276781) baseStart_276781 baseEnd_276781 := by
    simpa [prefixWord, tailWord_276781, baseEnd_276781] using wordTrace_append hprefix tailTrace_276781
  have hstable : (prefixWord ++ tailWord_276781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276781).length < 2 ^ (prefixWord ++ tailWord_276781).sum := by decide
  have hdescent : baseEnd_276781 < baseStart_276781 := by decide
  rcases family_descends (prefixWord ++ tailWord_276781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276785 : List Nat := [1, 2, 2, 3, 11]
def baseStart_276785 : Nat := 118140960795 + 276785 * 2 ^ 59
def prefixEnd_276785 : Nat := 4983230072969 + 3 ^ 40 * 276785 * 2
def baseEnd_276785 : Nat := 3119313974316703673297

theorem tailTrace_276785 : CollatzResearch.WordTrace tailWord_276785 prefixEnd_276785 3119313974316703673297 := by
  unfold tailWord_276785
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095178302262690959663809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6730118868175127306442539 10095178302262690959663809)
  ·
    refine ⟨7571383726697018219747857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10095178302262690959663809 7571383726697018219747857)
    ·
      refine ⟨5678537795022763664810893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7571383726697018219747857 5678537795022763664810893)
      ·
        refine ⟨2129451673133536374304085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5678537795022763664810893 2129451673133536374304085)
        ·
          refine ⟨3119313974316703673297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2129451673133536374304085 3119313974316703673297)
          ·
            rfl

theorem cell19_276785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 11].length) (baseStart_276785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276785 prefixEnd_276785 := by exact prefixLift 276785
  have htrace : WordTrace (prefixWord ++ tailWord_276785) baseStart_276785 baseEnd_276785 := by
    simpa [prefixWord, tailWord_276785, baseEnd_276785] using wordTrace_append hprefix tailTrace_276785
  have hstable : (prefixWord ++ tailWord_276785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276785).length < 2 ^ (prefixWord ++ tailWord_276785).sum := by decide
  have hdescent : baseEnd_276785 < baseStart_276785 := by decide
  rcases family_descends (prefixWord ++ tailWord_276785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276840 : List Nat := [2, 1, 4, 2, 2, 2, 6]
def baseStart_276840 : Nat := 118140960795 + 276840 * 2 ^ 59
def prefixEnd_276840 : Nat := 4983230072969 + 3 ^ 40 * 276840 * 2
def baseEnd_276840 : Nat := 28079404324109055985549

theorem tailTrace_276840 : CollatzResearch.WordTrace tailWord_276840 prefixEnd_276840 28079404324109055985549 := by
  unfold tailWord_276840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5048592158531717676457987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6731456211375623568610649 5048592158531717676457987)
  ·
    refine ⟨7572888237797576514686981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5048592158531717676457987 7572888237797576514686981)
    ·
      refine ⟨1419916544587045596503809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7572888237797576514686981 1419916544587045596503809)
      ·
        refine ⟨1064937408440284197377857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1419916544587045596503809 1064937408440284197377857)
        ·
          refine ⟨798703056330213148033393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064937408440284197377857 798703056330213148033393)
          ·
            refine ⟨599027292247659861025045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798703056330213148033393 599027292247659861025045)
            ·
              refine ⟨28079404324109055985549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 599027292247659861025045 28079404324109055985549)
              ·
                rfl

theorem cell19_276840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_276840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276840 prefixEnd_276840 := by exact prefixLift 276840
  have htrace : WordTrace (prefixWord ++ tailWord_276840) baseStart_276840 baseEnd_276840 := by
    simpa [prefixWord, tailWord_276840, baseEnd_276840] using wordTrace_append hprefix tailTrace_276840
  have hstable : (prefixWord ++ tailWord_276840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276840).length < 2 ^ (prefixWord ++ tailWord_276840).sum := by decide
  have hdescent : baseEnd_276840 < baseStart_276840 := by decide
  rcases family_descends (prefixWord ++ tailWord_276840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276876 : List Nat := [2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_276876 : Nat := 118140960795 + 276876 * 2 ^ 59
def prefixEnd_276876 : Nat := 4983230072969 + 3 ^ 40 * 276876 * 2
def baseEnd_276876 : Nat := 84249167226289751156549

theorem tailTrace_276876 : CollatzResearch.WordTrace tailWord_276876 prefixEnd_276876 84249167226289751156549 := by
  unfold tailWord_276876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049248672466506750613241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6732331563288675667484321 5049248672466506750613241)
  ·
    refine ⟨3786936504349880062959931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5049248672466506750613241 3786936504349880062959931)
    ·
      refine ⟨5680404756524820094439897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3786936504349880062959931 5680404756524820094439897)
      ·
        refine ⟨4260303567393615070829923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5680404756524820094439897 4260303567393615070829923)
        ·
          refine ⟨6390455351090422606244885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260303567393615070829923 6390455351090422606244885)
          ·
            refine ⟨299552594582363559667729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6390455351090422606244885 299552594582363559667729)
            ·
              refine ⟨224664445936772669750797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299552594582363559667729 224664445936772669750797)
              ·
                refine ⟨84249167226289751156549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224664445936772669750797 84249167226289751156549)
                ·
                  rfl

theorem cell19_276876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_276876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276876 prefixEnd_276876 := by exact prefixLift 276876
  have htrace : WordTrace (prefixWord ++ tailWord_276876) baseStart_276876 baseEnd_276876 := by
    simpa [prefixWord, tailWord_276876, baseEnd_276876] using wordTrace_append hprefix tailTrace_276876
  have hstable : (prefixWord ++ tailWord_276876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276876).length < 2 ^ (prefixWord ++ tailWord_276876).sum := by decide
  have hdescent : baseEnd_276876 < baseStart_276876 := by decide
  rcases family_descends (prefixWord ++ tailWord_276876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276899 : List Nat := [1, 1, 1, 4, 1, 4, 7]
def baseStart_276899 : Nat := 118140960795 + 276899 * 2 ^ 59
def prefixEnd_276899 : Nat := 4983230072969 + 3 ^ 40 * 276899 * 2
def baseEnd_276899 : Nat := 28085388592477504215125

theorem tailTrace_276899 : CollatzResearch.WordTrace tailWord_276899 prefixEnd_276899 28085388592477504215125 := by
  unfold tailWord_276899
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099336223849688429313751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6732890815899792286209167 10099336223849688429313751)
  ·
    refine ⟨15149004335774532643970627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10099336223849688429313751 15149004335774532643970627)
    ·
      refine ⟨22723506503661798965955941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15149004335774532643970627 22723506503661798965955941)
      ·
        refine ⟨4260657469436587306116739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22723506503661798965955941 4260657469436587306116739)
        ·
          refine ⟨6390986204154880959175109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260657469436587306116739 6390986204154880959175109)
          ·
            refine ⟨1198309913279040179845333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6390986204154880959175109 1198309913279040179845333)
            ·
              refine ⟨28085388592477504215125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1198309913279040179845333 28085388592477504215125)
              ·
                rfl

theorem cell19_276899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_276899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276899 prefixEnd_276899 := by exact prefixLift 276899
  have htrace : WordTrace (prefixWord ++ tailWord_276899) baseStart_276899 baseEnd_276899 := by
    simpa [prefixWord, tailWord_276899, baseEnd_276899] using wordTrace_append hprefix tailTrace_276899
  have hstable : (prefixWord ++ tailWord_276899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276899).length < 2 ^ (prefixWord ++ tailWord_276899).sum := by decide
  have hdescent : baseEnd_276899 < baseStart_276899 := by decide
  rcases family_descends (prefixWord ++ tailWord_276899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276937 : List Nat := [1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_276937 : Nat := 118140960795 + 276937 * 2 ^ 59
def prefixEnd_276937 : Nat := 4983230072969 + 3 ^ 40 * 276937 * 2
def baseEnd_276937 : Nat := 84267728601059683800827

theorem tailTrace_276937 : CollatzResearch.WordTrace tailWord_276937 prefixEnd_276937 84267728601059683800827 := by
  unfold tailWord_276937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10100722197712020919197065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6733814798474680612798043 10100722197712020919197065)
  ·
    refine ⟨7575541648284015689397799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10100722197712020919197065 7575541648284015689397799)
    ·
      refine ⟨11363312472426023534096699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7575541648284015689397799 11363312472426023534096699)
      ·
        refine ⟨17044968708639035301145049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11363312472426023534096699 17044968708639035301145049)
        ·
          refine ⟨12783726531479276475858787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17044968708639035301145049 12783726531479276475858787)
          ·
            refine ⟨19175589797218914713788181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12783726531479276475858787 19175589797218914713788181)
            ·
              refine ⟨898855771744636627208821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19175589797218914713788181 898855771744636627208821)
              ·
                refine ⟨84267728601059683800827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 898855771744636627208821 84267728601059683800827)
                ·
                  rfl

theorem cell19_276937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_276937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_276937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_276937 prefixEnd_276937 := by exact prefixLift 276937
  have htrace : WordTrace (prefixWord ++ tailWord_276937) baseStart_276937 baseEnd_276937 := by
    simpa [prefixWord, tailWord_276937, baseEnd_276937] using wordTrace_append hprefix tailTrace_276937
  have hstable : (prefixWord ++ tailWord_276937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276937).length < 2 ^ (prefixWord ++ tailWord_276937).sum := by decide
  have hdescent : baseEnd_276937 < baseStart_276937 := by decide
  rcases family_descends (prefixWord ++ tailWord_276937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277013 : List Nat := [1, 3, 2, 1, 3, 1, 8]
def baseStart_277013 : Nat := 118140960795 + 277013 * 2 ^ 59
def prefixEnd_277013 : Nat := 4983230072969 + 3 ^ 40 * 277013 * 2
def baseEnd_277013 : Nat := 28096951416104675370577

theorem tailTrace_277013 : CollatzResearch.WordTrace tailWord_277013 prefixEnd_277013 28096951416104675370577 := by
  unfold tailWord_277013
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103494145436685898963693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6735662763624457265975795 10103494145436685898963693)
  ·
    refine ⟨3788810304538757212111385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10103494145436685898963693 3788810304538757212111385)
    ·
      refine ⟨2841607728404067909083539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3788810304538757212111385 2841607728404067909083539)
      ·
        refine ⟨4262411592606101863625309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841607728404067909083539 4262411592606101863625309)
        ·
          refine ⟨1598404347227288198859491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4262411592606101863625309 1598404347227288198859491)
          ·
            refine ⟨2397606520840932298289237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598404347227288198859491 2397606520840932298289237)
            ·
              refine ⟨28096951416104675370577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2397606520840932298289237 28096951416104675370577)
              ·
                rfl

theorem cell19_277013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_277013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277013 prefixEnd_277013 := by exact prefixLift 277013
  have htrace : WordTrace (prefixWord ++ tailWord_277013) baseStart_277013 baseEnd_277013 := by
    simpa [prefixWord, tailWord_277013, baseEnd_277013] using wordTrace_append hprefix tailTrace_277013
  have hstable : (prefixWord ++ tailWord_277013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277013).length < 2 ^ (prefixWord ++ tailWord_277013).sum := by decide
  have hdescent : baseEnd_277013 < baseStart_277013 := by decide
  rcases family_descends (prefixWord ++ tailWord_277013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277070 : List Nat := [4, 1, 1, 1, 1, 2, 9]
def baseStart_277070 : Nat := 118140960795 + 277070 * 2 ^ 59
def prefixEnd_277070 : Nat := 4983230072969 + 3 ^ 40 * 277070 * 2
def baseEnd_277070 : Nat := 28102732827918260948303

theorem tailTrace_277070 : CollatzResearch.WordTrace tailWord_277070 prefixEnd_277070 28102732827918260948303 := by
  unfold tailWord_277070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263196638278773079223583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6737048737486789755859109 1263196638278773079223583)
  ·
    refine ⟨1894794957418159618835375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1263196638278773079223583 1894794957418159618835375)
    ·
      refine ⟨2842192436127239428253063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894794957418159618835375 2842192436127239428253063)
      ·
        refine ⟨4263288654190859142379595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842192436127239428253063 4263288654190859142379595)
        ·
          refine ⟨6394932981286288713569393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4263288654190859142379595 6394932981286288713569393)
          ·
            refine ⟨4796199735964716535177045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6394932981286288713569393 4796199735964716535177045)
            ·
              refine ⟨28102732827918260948303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4796199735964716535177045 28102732827918260948303)
              ·
                rfl

theorem cell19_277070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_277070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277070 prefixEnd_277070 := by exact prefixLift 277070
  have htrace : WordTrace (prefixWord ++ tailWord_277070) baseStart_277070 baseEnd_277070 := by
    simpa [prefixWord, tailWord_277070, baseEnd_277070] using wordTrace_append hprefix tailTrace_277070
  have hstable : (prefixWord ++ tailWord_277070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277070).length < 2 ^ (prefixWord ++ tailWord_277070).sum := by decide
  have hdescent : baseEnd_277070 < baseStart_277070 := by decide
  rcases family_descends (prefixWord ++ tailWord_277070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277089 : List Nat := [1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_277089 : Nat := 118140960795 + 277089 * 2 ^ 59
def prefixEnd_277089 : Nat := 4983230072969 + 3 ^ 40 * 277089 * 2
def baseEnd_277089 : Nat := 84313979895568368422635

theorem tailTrace_277089 : CollatzResearch.WordTrace tailWord_277089 prefixEnd_277089 84313979895568368422635 := by
  unfold tailWord_277089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10106266093161350878730321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6737510728774233919153547 10106266093161350878730321)
  ·
    refine ⟨7579699569871013159047741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10106266093161350878730321 7579699569871013159047741)
    ·
      refine ⟨2842387338701629934642903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7579699569871013159047741 2842387338701629934642903)
      ·
        refine ⟨4263581008052444901964355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842387338701629934642903 4263581008052444901964355)
        ·
          refine ⟨6395371512078667352946533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4263581008052444901964355 6395371512078667352946533)
          ·
            refine ⟨1199132158514750128677475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6395371512078667352946533 1199132158514750128677475)
            ·
              refine ⟨1798698237772125193016213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199132158514750128677475 1798698237772125193016213)
              ·
                refine ⟨84313979895568368422635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1798698237772125193016213 84313979895568368422635)
                ·
                  rfl

theorem cell19_277089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_277089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277089 prefixEnd_277089 := by exact prefixLift 277089
  have htrace : WordTrace (prefixWord ++ tailWord_277089) baseStart_277089 baseEnd_277089 := by
    simpa [prefixWord, tailWord_277089, baseEnd_277089] using wordTrace_append hprefix tailTrace_277089
  have hstable : (prefixWord ++ tailWord_277089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277089).length < 2 ^ (prefixWord ++ tailWord_277089).sum := by decide
  have hdescent : baseEnd_277089 < baseStart_277089 := by decide
  rcases family_descends (prefixWord ++ tailWord_277089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277159 : List Nat := [1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_277159 : Nat := 118140960795 + 277159 * 2 ^ 59
def prefixEnd_277159 : Nat := 4983230072969 + 3 ^ 40 * 277159 * 2
def baseEnd_277159 : Nat := 84335279833828946866889

theorem tailTrace_277159 : CollatzResearch.WordTrace tailWord_277159 prefixEnd_277159 84335279833828946866889 := by
  unfold tailWord_277159
  simp only [CollatzResearch.WordTrace]
  refine ⟨10108819202907752833778531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6739212801938501889185687 10108819202907752833778531)
  ·
    refine ⟨15163228804361629250667797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10108819202907752833778531 15163228804361629250667797)
    ·
      refine ⟨710776350204451371125053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15163228804361629250667797 710776350204451371125053)
      ·
        refine ⟨266541131326669264171895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 710776350204451371125053 266541131326669264171895)
        ·
          refine ⟨399811696990003896257843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266541131326669264171895 399811696990003896257843)
          ·
            refine ⟨599717545485005844386765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399811696990003896257843 599717545485005844386765)
            ·
              refine ⟨224894079556877191645037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599717545485005844386765 224894079556877191645037)
              ·
                refine ⟨84335279833828946866889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224894079556877191645037 84335279833828946866889)
                ·
                  rfl

theorem cell19_277159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_277159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277159 prefixEnd_277159 := by exact prefixLift 277159
  have htrace : WordTrace (prefixWord ++ tailWord_277159) baseStart_277159 baseEnd_277159 := by
    simpa [prefixWord, tailWord_277159, baseEnd_277159] using wordTrace_append hprefix tailTrace_277159
  have hstable : (prefixWord ++ tailWord_277159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277159).length < 2 ^ (prefixWord ++ tailWord_277159).sum := by decide
  have hdescent : baseEnd_277159 < baseStart_277159 := by decide
  rcases family_descends (prefixWord ++ tailWord_277159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277184 : List Nat := [2, 1, 1, 2, 4, 3, 6]
def baseStart_277184 : Nat := 118140960795 + 277184 * 2 ^ 59
def prefixEnd_277184 : Nat := 4983230072969 + 3 ^ 40 * 277184 * 2
def baseEnd_277184 : Nat := 28114295651545432103755

theorem tailTrace_277184 : CollatzResearch.WordTrace tailWord_277184 prefixEnd_277184 28114295651545432103755 := by
  unfold tailWord_277184
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054865513908591051719303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6739820685211454735625737 5054865513908591051719303)
  ·
    refine ⟨7582298270862886577578955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5054865513908591051719303 7582298270862886577578955)
    ·
      refine ⟨11373447406294329866368433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7582298270862886577578955 11373447406294329866368433)
      ·
        refine ⟨8530085554720747399776325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11373447406294329866368433 8530085554720747399776325)
        ·
          refine ⟨1599391041510140137458061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8530085554720747399776325 1599391041510140137458061)
          ·
            refine ⟨599771640566302551546773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1599391041510140137458061 599771640566302551546773)
            ·
              refine ⟨28114295651545432103755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 599771640566302551546773 28114295651545432103755)
              ·
                rfl

theorem cell19_277184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_277184 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277184 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277184 prefixEnd_277184 := by exact prefixLift 277184
  have htrace : WordTrace (prefixWord ++ tailWord_277184) baseStart_277184 baseEnd_277184 := by
    simpa [prefixWord, tailWord_277184, baseEnd_277184] using wordTrace_append hprefix tailTrace_277184
  have hstable : (prefixWord ++ tailWord_277184).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277184).length < 2 ^ (prefixWord ++ tailWord_277184).sum := by decide
  have hdescent : baseEnd_277184 < baseStart_277184 := by decide
  rcases family_descends (prefixWord ++ tailWord_277184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277220 : List Nat := [2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_277220 : Nat := 118140960795 + 277220 * 2 ^ 59
def prefixEnd_277220 : Nat := 4983230072969 + 3 ^ 40 * 277220 * 2
def baseEnd_277220 : Nat := 84353841208598879511167

theorem tailTrace_277220 : CollatzResearch.WordTrace tailWord_277220 prefixEnd_277220 84353841208598879511167 := by
  unfold tailWord_277220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5055522027843380125874557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6740696037124506834499409 5055522027843380125874557)
  ·
    refine ⟨1895820760441267547202959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5055522027843380125874557 1895820760441267547202959)
    ·
      refine ⟨2843731140661901320804439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895820760441267547202959 2843731140661901320804439)
      ·
        refine ⟨4265596710992851981206659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843731140661901320804439 4265596710992851981206659)
        ·
          refine ⟨6398395066489277971809989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4265596710992851981206659 6398395066489277971809989)
          ·
            refine ⟨1199699074966739619714373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6398395066489277971809989 1199699074966739619714373)
            ·
              refine ⟨224943576556263678696445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1199699074966739619714373 224943576556263678696445)
              ·
                refine ⟨84353841208598879511167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224943576556263678696445 84353841208598879511167)
                ·
                  rfl

theorem cell19_277220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_277220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277220 prefixEnd_277220 := by exact prefixLift 277220
  have htrace : WordTrace (prefixWord ++ tailWord_277220) baseStart_277220 baseEnd_277220 := by
    simpa [prefixWord, tailWord_277220, baseEnd_277220] using wordTrace_append hprefix tailTrace_277220
  have hstable : (prefixWord ++ tailWord_277220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277220).length < 2 ^ (prefixWord ++ tailWord_277220).sum := by decide
  have hdescent : baseEnd_277220 < baseStart_277220 := by decide
  rcases family_descends (prefixWord ++ tailWord_277220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277279 : List Nat := [1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_277279 : Nat := 118140960795 + 277279 * 2 ^ 59
def prefixEnd_277279 : Nat := 4983230072969 + 3 ^ 40 * 277279 * 2
def baseEnd_277279 : Nat := 84371794013704224199895

theorem tailTrace_277279 : CollatzResearch.WordTrace tailWord_277279 prefixEnd_277279 84371794013704224199895 := by
  unfold tailWord_277279
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113195962473013328146891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6742130641648675552097927 10113195962473013328146891)
  ·
    refine ⟨15169793943709519992220337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10113195962473013328146891 15169793943709519992220337)
    ·
      refine ⟨11377345457782139994165253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15169793943709519992220337 11377345457782139994165253)
      ·
        refine ⟨2133252273334151248905985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11377345457782139994165253 2133252273334151248905985)
        ·
          refine ⟨1599939205000613436679489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2133252273334151248905985 1599939205000613436679489)
          ·
            refine ⟨1199954403750460077509617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1599939205000613436679489 1199954403750460077509617)
            ·
              refine ⟨899965802812845058132213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199954403750460077509617 899965802812845058132213)
              ·
                refine ⟨84371794013704224199895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 899965802812845058132213 84371794013704224199895)
                ·
                  rfl

theorem cell19_277279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_277279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277279 prefixEnd_277279 := by exact prefixLift 277279
  have htrace : WordTrace (prefixWord ++ tailWord_277279) baseStart_277279 baseEnd_277279 := by
    simpa [prefixWord, tailWord_277279, baseEnd_277279] using wordTrace_append hprefix tailTrace_277279
  have hstable : (prefixWord ++ tailWord_277279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277279).length < 2 ^ (prefixWord ++ tailWord_277279).sum := by decide
  have hdescent : baseEnd_277279 < baseStart_277279 := by decide
  rcases family_descends (prefixWord ++ tailWord_277279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277332 : List Nat := [2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_277332 : Nat := 118140960795 + 277332 * 2 ^ 59
def prefixEnd_277332 : Nat := 4983230072969 + 3 ^ 40 * 277332 * 2
def baseEnd_277332 : Nat := 84387921109815805021973

theorem tailTrace_277332 : CollatzResearch.WordTrace tailWord_277332 prefixEnd_277332 84387921109815805021973 := by
  unfold tailWord_277332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057564515640501689913125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6743419354187335586550833 5057564515640501689913125)
  ·
    refine ⟨948293346682594066858711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5057564515640501689913125 948293346682594066858711)
    ·
      refine ⟨1422440020023891100288067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948293346682594066858711 1422440020023891100288067)
      ·
        refine ⟨2133660030035836650432101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422440020023891100288067 2133660030035836650432101)
        ·
          refine ⟨400061255631719371956019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2133660030035836650432101 400061255631719371956019)
          ·
            refine ⟨600091883447579057934029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400061255631719371956019 600091883447579057934029)
            ·
              refine ⟨225034456292842146725261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600091883447579057934029 225034456292842146725261)
              ·
                refine ⟨84387921109815805021973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225034456292842146725261 84387921109815805021973)
                ·
                  rfl

theorem cell19_277332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_277332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277332 prefixEnd_277332 := by exact prefixLift 277332
  have htrace : WordTrace (prefixWord ++ tailWord_277332) baseStart_277332 baseEnd_277332 := by
    simpa [prefixWord, tailWord_277332, baseEnd_277332] using wordTrace_append hprefix tailTrace_277332
  have hstable : (prefixWord ++ tailWord_277332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277332).length < 2 ^ (prefixWord ++ tailWord_277332).sum := by decide
  have hdescent : baseEnd_277332 < baseStart_277332 := by decide
  rcases family_descends (prefixWord ++ tailWord_277332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277410 : List Nat := [3, 3, 1, 2, 2, 3, 5]
def baseStart_277410 : Nat := 118140960795 + 277410 * 2 ^ 59
def prefixEnd_277410 : Nat := 4983230072969 + 3 ^ 40 * 277410 * 2
def baseEnd_277410 : Nat := 28137218442244911762809

theorem tailTrace_277410 : CollatzResearch.WordTrace tailWord_277410 prefixEnd_277410 28137218442244911762809 := by
  unfold tailWord_277410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529493481249605675291421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6745315949998948467443789 2529493481249605675291421)
  ·
    refine ⟨948560055468602128234283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2529493481249605675291421 948560055468602128234283)
    ·
      refine ⟨1422840083202903192351425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948560055468602128234283 1422840083202903192351425)
      ·
        refine ⟨1067130062402177394263569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1422840083202903192351425 1067130062402177394263569)
        ·
          refine ⟨800347546801633045697677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067130062402177394263569 800347546801633045697677)
          ·
            refine ⟨300130330050612392136629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800347546801633045697677 300130330050612392136629)
            ·
              refine ⟨28137218442244911762809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 300130330050612392136629 28137218442244911762809)
              ·
                rfl

theorem cell19_277410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_277410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277410 prefixEnd_277410 := by exact prefixLift 277410
  have htrace : WordTrace (prefixWord ++ tailWord_277410) baseStart_277410 baseEnd_277410 := by
    simpa [prefixWord, tailWord_277410, baseEnd_277410] using wordTrace_append hprefix tailTrace_277410
  have hstable : (prefixWord ++ tailWord_277410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277410).length < 2 ^ (prefixWord ++ tailWord_277410).sum := by decide
  have hdescent : baseEnd_277410 < baseStart_277410 := by decide
  rcases family_descends (prefixWord ++ tailWord_277410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277469 : List Nat := [1, 4, 3, 1, 2, 8]
def baseStart_277469 : Nat := 118140960795 + 277469 * 2 ^ 59
def prefixEnd_277469 : Nat := 4983230072969 + 3 ^ 40 * 277469 * 2
def baseEnd_277469 : Nat := 9381067570204453330795

theorem tailTrace_277469 : CollatzResearch.WordTrace tailWord_277469 prefixEnd_277469 9381067570204453330795 := by
  unfold tailWord_277469
  simp only [CollatzResearch.WordTrace]
  refine ⟨10120125831784675777563461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6746750554523117185042307 10120125831784675777563461)
  ·
    refine ⟨1897523593459626708293149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10120125831784675777563461 1897523593459626708293149)
    ·
      refine ⟨711571347547360015609931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1897523593459626708293149 711571347547360015609931)
      ·
        refine ⟨1067357021321040023414897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711571347547360015609931 1067357021321040023414897)
        ·
          refine ⟨800517765990780017561173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067357021321040023414897 800517765990780017561173)
          ·
            refine ⟨9381067570204453330795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 800517765990780017561173 9381067570204453330795)
            ·
              rfl

theorem cell19_277469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_277469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277469 prefixEnd_277469 := by exact prefixLift 277469
  have htrace : WordTrace (prefixWord ++ tailWord_277469) baseStart_277469 baseEnd_277469 := by
    simpa [prefixWord, tailWord_277469, baseEnd_277469] using wordTrace_append hprefix tailTrace_277469
  have hstable : (prefixWord ++ tailWord_277469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277469).length < 2 ^ (prefixWord ++ tailWord_277469).sum := by decide
  have hdescent : baseEnd_277469 < baseStart_277469 := by decide
  rcases family_descends (prefixWord ++ tailWord_277469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277471 : List Nat := [1, 1, 2, 3, 12]
def baseStart_277471 : Nat := 118140960795 + 277471 * 2 ^ 59
def prefixEnd_277471 : Nat := 4983230072969 + 3 ^ 40 * 277471 * 2
def baseEnd_277471 : Nat := 3127045063018691404915

theorem tailTrace_277471 : CollatzResearch.WordTrace tailWord_277471 prefixEnd_277471 3127045063018691404915 := by
  unfold tailWord_277471
  simp only [CollatzResearch.WordTrace]
  refine ⟨10120198777777430119136267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6746799185184953412757511 10120198777777430119136267)
  ·
    refine ⟨15180298166666145178704401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10120198777777430119136267 15180298166666145178704401)
    ·
      refine ⟨11385223624999608884028301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15180298166666145178704401 11385223624999608884028301)
      ·
        refine ⟨4269458859374853331510613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11385223624999608884028301 4269458859374853331510613)
        ·
          refine ⟨3127045063018691404915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4269458859374853331510613 3127045063018691404915)
          ·
            rfl

theorem cell19_277471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 12].length) (baseStart_277471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277471 prefixEnd_277471 := by exact prefixLift 277471
  have htrace : WordTrace (prefixWord ++ tailWord_277471) baseStart_277471 baseEnd_277471 := by
    simpa [prefixWord, tailWord_277471, baseEnd_277471] using wordTrace_append hprefix tailTrace_277471
  have hstable : (prefixWord ++ tailWord_277471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277471).length < 2 ^ (prefixWord ++ tailWord_277471).sum := by decide
  have hdescent : baseEnd_277471 < baseStart_277471 := by decide
  rcases family_descends (prefixWord ++ tailWord_277471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277505 : List Nat := [1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_277505 : Nat := 118140960795 + 277505 * 2 ^ 59
def prefixEnd_277505 : Nat := 4983230072969 + 3 ^ 40 * 277505 * 2
def baseEnd_277505 : Nat := 84440562385802663177057

theorem tailTrace_277505 : CollatzResearch.WordTrace tailWord_277505 prefixEnd_277505 84440562385802663177057 := by
  unfold tailWord_277505
  simp only [CollatzResearch.WordTrace]
  refine ⟨10121438859654253925873969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6747625906436169283915979 10121438859654253925873969)
  ·
    refine ⟨7591079144740690444405477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10121438859654253925873969 7591079144740690444405477)
    ·
      refine ⟨1423327339638879458326027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7591079144740690444405477 1423327339638879458326027)
      ·
        refine ⟨2134991009458319187489041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423327339638879458326027 2134991009458319187489041)
        ·
          refine ⟨1601243257093739390616781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134991009458319187489041 1601243257093739390616781)
          ·
            refine ⟨600466221410152271481293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1601243257093739390616781 600466221410152271481293)
            ·
              refine ⟨225174833028807101805485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600466221410152271481293 225174833028807101805485)
              ·
                refine ⟨84440562385802663177057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225174833028807101805485 84440562385802663177057)
                ·
                  rfl

theorem cell19_277505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_277505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277505 prefixEnd_277505 := by exact prefixLift 277505
  have htrace : WordTrace (prefixWord ++ tailWord_277505) baseStart_277505 baseEnd_277505 := by
    simpa [prefixWord, tailWord_277505, baseEnd_277505] using wordTrace_append hprefix tailTrace_277505
  have hstable : (prefixWord ++ tailWord_277505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277505).length < 2 ^ (prefixWord ++ tailWord_277505).sum := by decide
  have hdescent : baseEnd_277505 < baseStart_277505 := by decide
  rcases family_descends (prefixWord ++ tailWord_277505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277547 : List Nat := [1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_277547 : Nat := 118140960795 + 277547 * 2 ^ 59
def prefixEnd_277547 : Nat := 4983230072969 + 3 ^ 40 * 277547 * 2
def baseEnd_277547 : Nat := 84453342348759010243609

theorem tailTrace_277547 : CollatzResearch.WordTrace tailWord_277547 prefixEnd_277547 84453342348759010243609 := by
  unfold tailWord_277547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10122970725502095098902895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6748647150334730065935263 10122970725502095098902895)
  ·
    refine ⟨15184456088253142648354343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10122970725502095098902895 15184456088253142648354343)
    ·
      refine ⟨22776684132379713972531515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15184456088253142648354343 22776684132379713972531515)
      ·
        refine ⟨34165026198569570958797273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22776684132379713972531515 34165026198569570958797273)
        ·
          refine ⟨25623769648927178219097955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34165026198569570958797273 25623769648927178219097955)
          ·
            refine ⟨38435654473390767328646933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25623769648927178219097955 38435654473390767328646933)
            ·
              refine ⟨1801671303440192218530325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38435654473390767328646933 1801671303440192218530325)
              ·
                refine ⟨84453342348759010243609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1801671303440192218530325 84453342348759010243609)
                ·
                  rfl

theorem cell19_277547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_277547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277547 prefixEnd_277547 := by exact prefixLift 277547
  have htrace : WordTrace (prefixWord ++ tailWord_277547) baseStart_277547 baseEnd_277547 := by
    simpa [prefixWord, tailWord_277547, baseEnd_277547] using wordTrace_append hprefix tailTrace_277547
  have hstable : (prefixWord ++ tailWord_277547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277547).length < 2 ^ (prefixWord ++ tailWord_277547).sum := by decide
  have hdescent : baseEnd_277547 < baseStart_277547 := by decide
  rcases family_descends (prefixWord ++ tailWord_277547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277564 : List Nat := [2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_277564 : Nat := 118140960795 + 277564 * 2 ^ 59
def prefixEnd_277564 : Nat := 4983230072969 + 3 ^ 40 * 277564 * 2
def baseEnd_277564 : Nat := 84458515190908007865785

theorem tailTrace_277564 : CollatzResearch.WordTrace tailWord_277564 prefixEnd_277564 84458515190908007865785 := by
  unfold tailWord_277564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061795383220253501135873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6749060510960338001514497 5061795383220253501135873)
  ·
    refine ⟨3796346537415190125851905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5061795383220253501135873 3796346537415190125851905)
    ·
      refine ⟨2847259903061392594388929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3796346537415190125851905 2847259903061392594388929)
      ·
        refine ⟨2135444927296044445791697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2847259903061392594388929 2135444927296044445791697)
        ·
          refine ⟨1601583695472033334343773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2135444927296044445791697 1601583695472033334343773)
          ·
            refine ⟨600593885802012500378915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1601583695472033334343773 600593885802012500378915)
            ·
              refine ⟨900890828703018750568373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600593885802012500378915 900890828703018750568373)
              ·
                refine ⟨84458515190908007865785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 900890828703018750568373 84458515190908007865785)
                ·
                  rfl

theorem cell19_277564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_277564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277564 prefixEnd_277564 := by exact prefixLift 277564
  have htrace : WordTrace (prefixWord ++ tailWord_277564) baseStart_277564 baseEnd_277564 := by
    simpa [prefixWord, tailWord_277564, baseEnd_277564] using wordTrace_append hprefix tailTrace_277564
  have hstable : (prefixWord ++ tailWord_277564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277564).length < 2 ^ (prefixWord ++ tailWord_277564).sum := by decide
  have hdescent : baseEnd_277564 < baseStart_277564 := by decide
  rcases family_descends (prefixWord ++ tailWord_277564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277581 : List Nat := [1, 6, 1, 1, 1, 4, 5]
def baseStart_277581 : Nat := 118140960795 + 277581 * 2 ^ 59
def prefixEnd_277581 : Nat := 4983230072969 + 3 ^ 40 * 277581 * 2
def baseEnd_277581 : Nat := 28154562677685668495987

theorem tailTrace_277581 : CollatzResearch.WordTrace tailWord_277581 prefixEnd_277581 28154562677685668495987 := by
  unfold tailWord_277581
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124210807378918905640597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6749473871585945937093731 10124210807378918905640597)
  ·
    refine ⟨474572381595886823701903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10124210807378918905640597 474572381595886823701903)
    ·
      refine ⟨711858572393830235552855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474572381595886823701903 711858572393830235552855)
      ·
        refine ⟨1067787858590745353329283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711858572393830235552855 1067787858590745353329283)
        ·
          refine ⟨1601681787886118029993925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067787858590745353329283 1601681787886118029993925)
          ·
            refine ⟨300315335228647130623861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1601681787886118029993925 300315335228647130623861)
            ·
              refine ⟨28154562677685668495987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 300315335228647130623861 28154562677685668495987)
              ·
                rfl

theorem cell19_277581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_277581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277581 prefixEnd_277581 := by exact prefixLift 277581
  have htrace : WordTrace (prefixWord ++ tailWord_277581) baseStart_277581 baseEnd_277581 := by
    simpa [prefixWord, tailWord_277581, baseEnd_277581] using wordTrace_append hprefix tailTrace_277581
  have hstable : (prefixWord ++ tailWord_277581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277581).length < 2 ^ (prefixWord ++ tailWord_277581).sum := by decide
  have hdescent : baseEnd_277581 < baseStart_277581 := by decide
  rcases family_descends (prefixWord ++ tailWord_277581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277585 : List Nat := [1, 2, 2, 1, 3, 1, 9]
def baseStart_277585 : Nat := 118140960795 + 277585 * 2 ^ 59
def prefixEnd_277585 : Nat := 4983230072969 + 3 ^ 40 * 277585 * 2
def baseEnd_277585 : Nat := 28154968390795393799687

theorem tailTrace_277585 : CollatzResearch.WordTrace tailWord_277585 prefixEnd_277585 28154968390795393799687 := by
  unfold tailWord_277585
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124356699364427588786209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6749571132909618392524139 10124356699364427588786209)
  ·
    refine ⟨7593267524523320691589657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10124356699364427588786209 7593267524523320691589657)
    ·
      refine ⟨5694950643392490518692243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7593267524523320691589657 5694950643392490518692243)
      ·
        refine ⟨8542425965088735778038365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694950643392490518692243 8542425965088735778038365)
        ·
          refine ⟨3203409736908275916764387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8542425965088735778038365 3203409736908275916764387)
          ·
            refine ⟨4805114605362413875146581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203409736908275916764387 4805114605362413875146581)
            ·
              refine ⟨28154968390795393799687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4805114605362413875146581 28154968390795393799687)
              ·
                rfl

theorem cell19_277585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_277585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277585 prefixEnd_277585 := by exact prefixLift 277585
  have htrace : WordTrace (prefixWord ++ tailWord_277585) baseStart_277585 baseEnd_277585 := by
    simpa [prefixWord, tailWord_277585, baseEnd_277585] using wordTrace_append hprefix tailTrace_277585
  have hstable : (prefixWord ++ tailWord_277585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277585).length < 2 ^ (prefixWord ++ tailWord_277585).sum := by decide
  have hdescent : baseEnd_277585 < baseStart_277585 := by decide
  rcases family_descends (prefixWord ++ tailWord_277585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277598 : List Nat := [4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_277598 : Nat := 118140960795 + 277598 * 2 ^ 59
def prefixEnd_277598 : Nat := 4983230072969 + 3 ^ 40 * 277598 * 2
def baseEnd_277598 : Nat := 84468860875206003110137

theorem tailTrace_277598 : CollatzResearch.WordTrace tailWord_277598 prefixEnd_277598 84468860875206003110137 := by
  unfold tailWord_277598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265603856039666351126181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6749887232211553872672965 1265603856039666351126181)
  ·
    refine ⟨237300723007437440836159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1265603856039666351126181 237300723007437440836159)
    ·
      refine ⟨355951084511156161254239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237300723007437440836159 355951084511156161254239)
      ·
        refine ⟨533926626766734241881359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355951084511156161254239 533926626766734241881359)
        ·
          refine ⟨800889940150101362822039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533926626766734241881359 800889940150101362822039)
          ·
            refine ⟨1201334910225152044233059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800889940150101362822039 1201334910225152044233059)
            ·
              refine ⟨1802002365337728066349589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201334910225152044233059 1802002365337728066349589)
              ·
                refine ⟨84468860875206003110137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1802002365337728066349589 84468860875206003110137)
                ·
                  rfl

theorem cell19_277598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_277598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277598 prefixEnd_277598 := by exact prefixLift 277598
  have htrace : WordTrace (prefixWord ++ tailWord_277598) baseStart_277598 baseEnd_277598 := by
    simpa [prefixWord, tailWord_277598, baseEnd_277598] using wordTrace_append hprefix tailTrace_277598
  have hstable : (prefixWord ++ tailWord_277598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277598).length < 2 ^ (prefixWord ++ tailWord_277598).sum := by decide
  have hdescent : baseEnd_277598 < baseStart_277598 := by decide
  rcases family_descends (prefixWord ++ tailWord_277598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277623 : List Nat := [1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_277623 : Nat := 118140960795 + 277623 * 2 ^ 59
def prefixEnd_277623 : Nat := 4983230072969 + 3 ^ 40 * 277623 * 2
def baseEnd_277623 : Nat := 84476467996013352554513

theorem tailTrace_277623 : CollatzResearch.WordTrace tailWord_277623 prefixEnd_277623 84476467996013352554513 := by
  unfold tailWord_277623
  simp only [CollatzResearch.WordTrace]
  refine ⟨10125742673226760078669523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6750495115484506719113015 10125742673226760078669523)
  ·
    refine ⟨15188614009840140118004285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10125742673226760078669523 15188614009840140118004285)
    ·
      refine ⟨5695730253690052544251607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15188614009840140118004285 5695730253690052544251607)
      ·
        refine ⟨8543595380535078816377411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5695730253690052544251607 8543595380535078816377411)
        ·
          refine ⟨12815393070802618224566117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8543595380535078816377411 12815393070802618224566117)
          ·
            refine ⟨2402886200775490917106147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12815393070802618224566117 2402886200775490917106147)
            ·
              refine ⟨3604329301163236375659221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402886200775490917106147 3604329301163236375659221)
              ·
                refine ⟨84476467996013352554513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3604329301163236375659221 84476467996013352554513)
                ·
                  rfl

theorem cell19_277623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_277623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277623 prefixEnd_277623 := by exact prefixLift 277623
  have htrace : WordTrace (prefixWord ++ tailWord_277623) baseStart_277623 baseEnd_277623 := by
    simpa [prefixWord, tailWord_277623, baseEnd_277623] using wordTrace_append hprefix tailTrace_277623
  have hstable : (prefixWord ++ tailWord_277623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277623).length < 2 ^ (prefixWord ++ tailWord_277623).sum := by decide
  have hdescent : baseEnd_277623 < baseStart_277623 := by decide
  rcases family_descends (prefixWord ++ tailWord_277623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277640 : List Nat := [2, 1, 3, 4, 2, 7]
def baseStart_277640 : Nat := 118140960795 + 277640 * 2 ^ 59
def prefixEnd_277640 : Nat := 4983230072969 + 3 ^ 40 * 277640 * 2
def baseEnd_277640 : Nat := 9386848982018038908521

theorem tailTrace_277640 : CollatzResearch.WordTrace tailWord_277640 prefixEnd_277640 9386848982018038908521 := by
  unfold tailWord_277640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5063181357082585991019187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6750908476110114654692249 5063181357082585991019187)
  ·
    refine ⟨7594772035623878986528781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5063181357082585991019187 7594772035623878986528781)
    ·
      refine ⟨2848039513358954619948293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7594772035623878986528781 2848039513358954619948293)
      ·
        refine ⟨534007408754803991240305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2848039513358954619948293 534007408754803991240305)
        ·
          refine ⟨400505556566102993430229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534007408754803991240305 400505556566102993430229)
          ·
            refine ⟨9386848982018038908521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 400505556566102993430229 9386848982018038908521)
            ·
              rfl

theorem cell19_277640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_277640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277640 prefixEnd_277640 := by exact prefixLift 277640
  have htrace : WordTrace (prefixWord ++ tailWord_277640) baseStart_277640 baseEnd_277640 := by
    simpa [prefixWord, tailWord_277640, baseEnd_277640] using wordTrace_append hprefix tailTrace_277640
  have hstable : (prefixWord ++ tailWord_277640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277640).length < 2 ^ (prefixWord ++ tailWord_277640).sum := by decide
  have hdescent : baseEnd_277640 < baseStart_277640 := by decide
  rcases family_descends (prefixWord ++ tailWord_277640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277674 : List Nat := [3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_277674 : Nat := 118140960795 + 277674 * 2 ^ 59
def prefixEnd_277674 : Nat := 4983230072969 + 3 ^ 40 * 277674 * 2
def baseEnd_277674 : Nat := 84491986522460345421041

theorem tailTrace_277674 : CollatzResearch.WordTrace tailWord_277674 prefixEnd_277674 84491986522460345421041 := by
  unfold tailWord_277674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531900699010498947194019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6751735197361330525850717 2531900699010498947194019)
  ·
    refine ⟨3797851048515748420791029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2531900699010498947194019 3797851048515748420791029)
    ·
      refine ⟨356048535798351414449159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3797851048515748420791029 356048535798351414449159)
      ·
        refine ⟨534072803697527121673739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356048535798351414449159 534072803697527121673739)
        ·
          refine ⟨801109205546290682510609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534072803697527121673739 801109205546290682510609)
          ·
            refine ⟨600831904159718011882957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801109205546290682510609 600831904159718011882957)
            ·
              refine ⟨225311964059894254456109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600831904159718011882957 225311964059894254456109)
              ·
                refine ⟨84491986522460345421041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225311964059894254456109 84491986522460345421041)
                ·
                  rfl

theorem cell19_277674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_277674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277674 prefixEnd_277674 := by exact prefixLift 277674
  have htrace : WordTrace (prefixWord ++ tailWord_277674) baseStart_277674 baseEnd_277674 := by
    simpa [prefixWord, tailWord_277674, baseEnd_277674] using wordTrace_append hprefix tailTrace_277674
  have hstable : (prefixWord ++ tailWord_277674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277674).length < 2 ^ (prefixWord ++ tailWord_277674).sum := by decide
  have hdescent : baseEnd_277674 < baseStart_277674 := by decide
  rcases family_descends (prefixWord ++ tailWord_277674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277748 : List Nat := [2, 6, 1, 2, 1, 2, 5]
def baseStart_277748 : Nat := 118140960795 + 277748 * 2 ^ 59
def prefixEnd_277748 : Nat := 4983230072969 + 3 ^ 40 * 277748 * 2
def baseEnd_277748 : Nat := 28171501200016699925465

theorem tailTrace_277748 : CollatzResearch.WordTrace tailWord_277748 prefixEnd_277748 28171501200016699925465 := by
  unfold tailWord_277748
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065150898886953213484949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6753534531849270951313265 5065150898886953213484949)
  ·
    refine ⟨237428948385325931882107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5065150898886953213484949 237428948385325931882107)
    ·
      refine ⟨356143422577988897823161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237428948385325931882107 356143422577988897823161)
      ·
        refine ⟨267107566933491673367371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356143422577988897823161 267107566933491673367371)
        ·
          refine ⟨400661350400237510051057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267107566933491673367371 400661350400237510051057)
          ·
            refine ⟨300496012800178132538293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400661350400237510051057 300496012800178132538293)
            ·
              refine ⟨28171501200016699925465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 300496012800178132538293 28171501200016699925465)
              ·
                rfl

theorem cell19_277748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_277748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277748 prefixEnd_277748 := by exact prefixLift 277748
  have htrace : WordTrace (prefixWord ++ tailWord_277748) baseStart_277748 baseEnd_277748 := by
    simpa [prefixWord, tailWord_277748, baseEnd_277748] using wordTrace_append hprefix tailTrace_277748
  have hstable : (prefixWord ++ tailWord_277748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277748).length < 2 ^ (prefixWord ++ tailWord_277748).sum := by decide
  have hdescent : baseEnd_277748 < baseStart_277748 := by decide
  rcases family_descends (prefixWord ++ tailWord_277748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277813 : List Nat := [1, 3, 3, 1, 2, 9]
def baseStart_277813 : Nat := 118140960795 + 277813 * 2 ^ 59
def prefixEnd_277813 : Nat := 4983230072969 + 3 ^ 40 * 277813 * 2
def baseEnd_277813 : Nat := 9392698012683245370197

theorem tailTrace_277813 : CollatzResearch.WordTrace tailWord_277813 prefixEnd_277813 9392698012683245370197 := by
  unfold tailWord_277813
  simp only [CollatzResearch.WordTrace]
  refine ⟨10132672542538422528086093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6755115028358948352057395 10132672542538422528086093)
  ·
    refine ⟨3799752203451908448032285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10132672542538422528086093 3799752203451908448032285)
    ·
      refine ⟨1424907076294465668012107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3799752203451908448032285 1424907076294465668012107)
      ·
        refine ⟨2137360614441698502018161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424907076294465668012107 2137360614441698502018161)
        ·
          refine ⟨1603020460831273876513621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2137360614441698502018161 1603020460831273876513621)
          ·
            refine ⟨9392698012683245370197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1603020460831273876513621 9392698012683245370197)
            ·
              rfl

theorem cell19_277813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_277813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277813 prefixEnd_277813 := by exact prefixLift 277813
  have htrace : WordTrace (prefixWord ++ tailWord_277813) baseStart_277813 baseEnd_277813 := by
    simpa [prefixWord, tailWord_277813, baseEnd_277813] using wordTrace_append hprefix tailTrace_277813
  have hstable : (prefixWord ++ tailWord_277813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277813).length < 2 ^ (prefixWord ++ tailWord_277813).sum := by decide
  have hdescent : baseEnd_277813 < baseStart_277813 := by decide
  rcases family_descends (prefixWord ++ tailWord_277813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277828 : List Nat := [2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_277828 : Nat := 118140960795 + 277828 * 2 ^ 59
def prefixEnd_277828 : Nat := 4983230072969 + 3 ^ 40 * 277828 * 2
def baseEnd_277828 : Nat := 84538846386633617998399

theorem tailTrace_277828 : CollatzResearch.WordTrace tailWord_277828 prefixEnd_277828 84538846386633617998399 := by
  unfold tailWord_277828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066609818742040044941069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6755479758322720059921425 5066609818742040044941069)
  ·
    refine ⟨1899978682028265016852901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5066609818742040044941069 1899978682028265016852901)
    ·
      refine ⟨356246002880299690659919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1899978682028265016852901 356246002880299690659919)
      ·
        refine ⟨534369004320449535989879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356246002880299690659919 534369004320449535989879)
        ·
          refine ⟨801553506480674303984819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534369004320449535989879 801553506480674303984819)
          ·
            refine ⟨1202330259721011455977229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801553506480674303984819 1202330259721011455977229)
            ·
              refine ⟨450873847395379295991461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202330259721011455977229 450873847395379295991461)
              ·
                refine ⟨84538846386633617998399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450873847395379295991461 84538846386633617998399)
                ·
                  rfl

theorem cell19_277828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_277828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277828 prefixEnd_277828 := by exact prefixLift 277828
  have htrace : WordTrace (prefixWord ++ tailWord_277828) baseStart_277828 baseEnd_277828 := by
    simpa [prefixWord, tailWord_277828, baseEnd_277828] using wordTrace_append hprefix tailTrace_277828
  have hstable : (prefixWord ++ tailWord_277828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277828).length < 2 ^ (prefixWord ++ tailWord_277828).sum := by decide
  have hdescent : baseEnd_277828 < baseStart_277828 := by decide
  rcases family_descends (prefixWord ++ tailWord_277828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277902 : List Nat := [4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_277902 : Nat := 118140960795 + 277902 * 2 ^ 59
def prefixEnd_277902 : Nat := 4983230072969 + 3 ^ 40 * 277902 * 2
def baseEnd_277902 : Nat := 84561363464223372353753

theorem tailTrace_277902 : CollatzResearch.WordTrace tailWord_277902 prefixEnd_277902 84561363464223372353753 := by
  unfold tailWord_277902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266989829901998841009495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6757279092810660485383973 1266989829901998841009495)
  ·
    refine ⟨1900484744852998261514243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1266989829901998841009495 1900484744852998261514243)
    ·
      refine ⟨2850727117279497392271365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900484744852998261514243 2850727117279497392271365)
      ·
        refine ⟨534511334489905761050881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2850727117279497392271365 534511334489905761050881)
        ·
          refine ⟨400883500867429320788161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534511334489905761050881 400883500867429320788161)
          ·
            refine ⟨300662625650571990591121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400883500867429320788161 300662625650571990591121)
            ·
              refine ⟨225496969237928992943341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300662625650571990591121 225496969237928992943341)
              ·
                refine ⟨84561363464223372353753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225496969237928992943341 84561363464223372353753)
                ·
                  rfl

theorem cell19_277902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_277902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277902 prefixEnd_277902 := by exact prefixLift 277902
  have htrace : WordTrace (prefixWord ++ tailWord_277902) baseStart_277902 baseEnd_277902 := by
    simpa [prefixWord, tailWord_277902, baseEnd_277902] using wordTrace_append hprefix tailTrace_277902
  have hstable : (prefixWord ++ tailWord_277902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277902).length < 2 ^ (prefixWord ++ tailWord_277902).sum := by decide
  have hdescent : baseEnd_277902 < baseStart_277902 := by decide
  rcases family_descends (prefixWord ++ tailWord_277902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277997 : List Nat := [1, 5, 1, 3, 3, 1, 1, 4]
def baseStart_277997 : Nat := 118140960795 + 277997 * 2 ^ 59
def prefixEnd_277997 : Nat := 4983230072969 + 3 ^ 40 * 277997 * 2
def baseEnd_277997 : Nat := 84590270523291300242383

theorem tailTrace_277997 : CollatzResearch.WordTrace tailWord_277997 prefixEnd_277997 84590270523291300242383 := by
  unfold tailWord_277997
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139383573871821952784245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6759589049247881301856163 10139383573871821952784245)
  ·
    refine ⟨950567210050483308073523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10139383573871821952784245 950567210050483308073523)
    ·
      refine ⟨1425850815075724962110285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950567210050483308073523 1425850815075724962110285)
      ·
        refine ⟨534694055653396860791357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1425850815075724962110285 534694055653396860791357)
        ·
          refine ⟨200510270870023822796759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 534694055653396860791357 200510270870023822796759)
          ·
            refine ⟨300765406305035734195139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200510270870023822796759 300765406305035734195139)
            ·
              refine ⟨451148109457553601292709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300765406305035734195139 451148109457553601292709)
              ·
                refine ⟨84590270523291300242383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451148109457553601292709 84590270523291300242383)
                ·
                  rfl

theorem cell19_277997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_277997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_277997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_277997 prefixEnd_277997 := by exact prefixLift 277997
  have htrace : WordTrace (prefixWord ++ tailWord_277997) baseStart_277997 baseEnd_277997 := by
    simpa [prefixWord, tailWord_277997, baseEnd_277997] using wordTrace_append hprefix tailTrace_277997
  have hstable : (prefixWord ++ tailWord_277997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277997).length < 2 ^ (prefixWord ++ tailWord_277997).sum := by decide
  have hdescent : baseEnd_277997 < baseStart_277997 := by decide
  rcases family_descends (prefixWord ++ tailWord_277997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278001 : List Nat := [1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_278001 : Nat := 118140960795 + 278001 * 2 ^ 59
def prefixEnd_278001 : Nat := 4983230072969 + 3 ^ 40 * 278001 * 2
def baseEnd_278001 : Nat := 84591487662620476153483

theorem tailTrace_278001 : CollatzResearch.WordTrace tailWord_278001 prefixEnd_278001 84591487662620476153483 := by
  unfold tailWord_278001
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139529465857330635929857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6759686310571553757286571 10139529465857330635929857)
  ·
    refine ⟨7604647099392997976947393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10139529465857330635929857 7604647099392997976947393)
    ·
      refine ⟨5703485324544748482710545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7604647099392997976947393 5703485324544748482710545)
      ·
        refine ⟨4277613993408561362032909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5703485324544748482710545 4277613993408561362032909)
        ·
          refine ⟨1604105247528210510762341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4277613993408561362032909 1604105247528210510762341)
          ·
            refine ⟨300769733911539470767939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1604105247528210510762341 300769733911539470767939)
            ·
              refine ⟨451154600867309206151909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300769733911539470767939 451154600867309206151909)
              ·
                refine ⟨84591487662620476153483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451154600867309206151909 84591487662620476153483)
                ·
                  rfl

theorem cell19_278001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_278001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278001 prefixEnd_278001 := by exact prefixLift 278001
  have htrace : WordTrace (prefixWord ++ tailWord_278001) baseStart_278001 baseEnd_278001 := by
    simpa [prefixWord, tailWord_278001, baseEnd_278001] using wordTrace_append hprefix tailTrace_278001
  have hstable : (prefixWord ++ tailWord_278001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278001).length < 2 ^ (prefixWord ++ tailWord_278001).sum := by decide
  have hdescent : baseEnd_278001 < baseStart_278001 := by decide
  rcases family_descends (prefixWord ++ tailWord_278001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278077 : List Nat := [1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_278077 : Nat := 118140960795 + 278077 * 2 ^ 59
def prefixEnd_278077 : Nat := 4983230072969 + 3 ^ 40 * 278077 * 2
def baseEnd_278077 : Nat := 84614613309874818464387

theorem tailTrace_278077 : CollatzResearch.WordTrace tailWord_278077 prefixEnd_278077 84614613309874818464387 := by
  unfold tailWord_278077
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142301413581995615696485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6761534275721330410464323 10142301413581995615696485)
  ·
    refine ⟨1901681515046624177943091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10142301413581995615696485 1901681515046624177943091)
    ·
      refine ⟨2852522272569936266914637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901681515046624177943091 2852522272569936266914637)
      ·
        refine ⟨1069695852213726100092989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2852522272569936266914637 1069695852213726100092989)
        ·
          refine ⟨401135944580147287534871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1069695852213726100092989 401135944580147287534871)
          ·
            refine ⟨601703916870220931302307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401135944580147287534871 601703916870220931302307)
            ·
              refine ⟨902555875305331396953461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601703916870220931302307 902555875305331396953461)
              ·
                refine ⟨84614613309874818464387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902555875305331396953461 84614613309874818464387)
                ·
                  rfl

theorem cell19_278077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_278077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278077 prefixEnd_278077 := by exact prefixLift 278077
  have htrace : WordTrace (prefixWord ++ tailWord_278077) baseStart_278077 baseEnd_278077 := by
    simpa [prefixWord, tailWord_278077, baseEnd_278077] using wordTrace_append hprefix tailTrace_278077
  have hstable : (prefixWord ++ tailWord_278077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278077).length < 2 ^ (prefixWord ++ tailWord_278077).sum := by decide
  have hdescent : baseEnd_278077 < baseStart_278077 := by decide
  rcases family_descends (prefixWord ++ tailWord_278077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278079 : List Nat := [1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_278079 : Nat := 118140960795 + 278079 * 2 ^ 59
def prefixEnd_278079 : Nat := 4983230072969 + 3 ^ 40 * 278079 * 2
def baseEnd_278079 : Nat := 84615221879539406419937

theorem tailTrace_278079 : CollatzResearch.WordTrace tailWord_278079 prefixEnd_278079 84615221879539406419937 := by
  unfold tailWord_278079
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142374359574749957269291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6761582906383166638179527 10142374359574749957269291)
  ·
    refine ⟨15213561539362124935903937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10142374359574749957269291 15213561539362124935903937)
    ·
      refine ⟨11410171154521593701927953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15213561539362124935903937 11410171154521593701927953)
      ·
        refine ⟨8557628365891195276445965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11410171154521593701927953 8557628365891195276445965)
        ·
          refine ⟨3209110637209198228667237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8557628365891195276445965 3209110637209198228667237)
          ·
            refine ⟨601708244476724667875107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3209110637209198228667237 601708244476724667875107)
            ·
              refine ⟨902562366715087001812661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601708244476724667875107 902562366715087001812661)
              ·
                refine ⟨84615221879539406419937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902562366715087001812661 84615221879539406419937)
                ·
                  rfl

theorem cell19_278079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_278079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278079 prefixEnd_278079 := by exact prefixLift 278079
  have htrace : WordTrace (prefixWord ++ tailWord_278079) baseStart_278079 baseEnd_278079 := by
    simpa [prefixWord, tailWord_278079, baseEnd_278079] using wordTrace_append hprefix tailTrace_278079
  have hstable : (prefixWord ++ tailWord_278079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278079).length < 2 ^ (prefixWord ++ tailWord_278079).sum := by decide
  have hdescent : baseEnd_278079 < baseStart_278079 := by decide
  rcases family_descends (prefixWord ++ tailWord_278079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278098 : List Nat := [3, 2, 2, 1, 2, 2, 7]
def baseStart_278098 : Nat := 118140960795 + 278098 * 2 ^ 59
def prefixEnd_278098 : Nat := 4983230072969 + 3 ^ 40 * 278098 * 2
def baseEnd_278098 : Nat := 28207001097117663999221

theorem tailTrace_278098 : CollatzResearch.WordTrace tailWord_278098 prefixEnd_278098 28207001097117663999221 := by
  unfold tailWord_278098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535766836626479050552737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6762044897670610801473965 2535766836626479050552737)
  ·
    refine ⟨1901825127469859287914553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2535766836626479050552737 1901825127469859287914553)
    ·
      refine ⟨1426368845602394465935915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1901825127469859287914553 1426368845602394465935915)
      ·
        refine ⟨2139553268403591698903873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426368845602394465935915 2139553268403591698903873)
        ·
          refine ⟨1604664951302693774177905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2139553268403591698903873 1604664951302693774177905)
          ·
            refine ⟨1203498713477020330633429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1604664951302693774177905 1203498713477020330633429)
            ·
              refine ⟨28207001097117663999221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1203498713477020330633429 28207001097117663999221)
              ·
                rfl

theorem cell19_278098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_278098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278098 prefixEnd_278098 := by exact prefixLift 278098
  have htrace : WordTrace (prefixWord ++ tailWord_278098) baseStart_278098 baseEnd_278098 := by
    simpa [prefixWord, tailWord_278098, baseEnd_278098] using wordTrace_append hprefix tailTrace_278098
  have hstable : (prefixWord ++ tailWord_278098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278098).length < 2 ^ (prefixWord ++ tailWord_278098).sum := by decide
  have hdescent : baseEnd_278098 < baseStart_278098 := by decide
  rcases family_descends (prefixWord ++ tailWord_278098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278117 : List Nat := [1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_278117 : Nat := 118140960795 + 278117 * 2 ^ 59
def prefixEnd_278117 : Nat := 4983230072969 + 3 ^ 40 * 278117 * 2
def baseEnd_278117 : Nat := 84626784703166577575389

theorem tailTrace_278117 : CollatzResearch.WordTrace tailWord_278117 prefixEnd_278117 84626784703166577575389 := by
  unfold tailWord_278117
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143760333437082447152605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6762506888958054964768403 10143760333437082447152605)
  ·
    refine ⟨3803910125038905917682227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10143760333437082447152605 3803910125038905917682227)
    ·
      refine ⟨5705865187558358876523341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3803910125038905917682227 5705865187558358876523341)
      ·
        refine ⟨2139699445334384578696253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5705865187558358876523341 2139699445334384578696253)
        ·
          refine ⟨802387292000394217011095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2139699445334384578696253 802387292000394217011095)
          ·
            refine ⟨1203580938000591325516643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802387292000394217011095 1203580938000591325516643)
            ·
              refine ⟨1805371407000886988274965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203580938000591325516643 1805371407000886988274965)
              ·
                refine ⟨84626784703166577575389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1805371407000886988274965 84626784703166577575389)
                ·
                  rfl

theorem cell19_278117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_278117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278117 prefixEnd_278117 := by exact prefixLift 278117
  have htrace : WordTrace (prefixWord ++ tailWord_278117) baseStart_278117 baseEnd_278117 := by
    simpa [prefixWord, tailWord_278117, baseEnd_278117] using wordTrace_append hprefix tailTrace_278117
  have hstable : (prefixWord ++ tailWord_278117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278117).length < 2 ^ (prefixWord ++ tailWord_278117).sum := by decide
  have hdescent : baseEnd_278117 < baseStart_278117 := by decide
  rcases family_descends (prefixWord ++ tailWord_278117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278134 : List Nat := [5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_278134 : Nat := 118140960795 + 278134 * 2 ^ 59
def prefixEnd_278134 : Nat := 4983230072969 + 3 ^ 40 * 278134 * 2
def baseEnd_278134 : Nat := 84631957545315575197565

theorem tailTrace_278134 : CollatzResearch.WordTrace tailWord_278134 prefixEnd_278134 84631957545315575197565 := by
  unfold tailWord_278134
  simp only [CollatzResearch.WordTrace]
  refine ⟨634023773398468396907591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6762920249583662900347637 634023773398468396907591)
  ·
    refine ⟨951035660097702595361387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634023773398468396907591 951035660097702595361387)
    ·
      refine ⟨1426553490146553893042081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 951035660097702595361387 1426553490146553893042081)
      ·
        refine ⟨1069915117609915419781561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1426553490146553893042081 1069915117609915419781561)
        ·
          refine ⟨802436338207436564836171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069915117609915419781561 802436338207436564836171)
          ·
            refine ⟨1203654507311154847254257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802436338207436564836171 1203654507311154847254257)
            ·
              refine ⟨902740880483366135440693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203654507311154847254257 902740880483366135440693)
              ·
                refine ⟨84631957545315575197565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902740880483366135440693 84631957545315575197565)
                ·
                  rfl

theorem cell19_278134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_278134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278134 prefixEnd_278134 := by exact prefixLift 278134
  have htrace : WordTrace (prefixWord ++ tailWord_278134) baseStart_278134 baseEnd_278134 := by
    simpa [prefixWord, tailWord_278134, baseEnd_278134] using wordTrace_append hprefix tailTrace_278134
  have hstable : (prefixWord ++ tailWord_278134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278134).length < 2 ^ (prefixWord ++ tailWord_278134).sum := by decide
  have hdescent : baseEnd_278134 < baseStart_278134 := by decide
  rcases family_descends (prefixWord ++ tailWord_278134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278157 : List Nat := [1, 18]
def baseStart_278157 : Nat := 118140960795 + 278157 * 2 ^ 59
def prefixEnd_278157 : Nat := 4983230072969 + 3 ^ 40 * 278157 * 2
def baseEnd_278157 : Nat := 116102820434099227279

theorem tailTrace_278157 : CollatzResearch.WordTrace tailWord_278157 prefixEnd_278157 116102820434099227279 := by
  unfold tailWord_278157
  simp only [CollatzResearch.WordTrace]
  refine ⟨10145219253292169278608725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6763479502194779519072483 10145219253292169278608725)
  ·
    refine ⟨116102820434099227279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 18 10145219253292169278608725 116102820434099227279)
    ·
      rfl

theorem cell19_278157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 18].length) (baseStart_278157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278157 prefixEnd_278157 := by exact prefixLift 278157
  have htrace : WordTrace (prefixWord ++ tailWord_278157) baseStart_278157 baseEnd_278157 := by
    simpa [prefixWord, tailWord_278157, baseEnd_278157] using wordTrace_append hprefix tailTrace_278157
  have hstable : (prefixWord ++ tailWord_278157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278157).length < 2 ^ (prefixWord ++ tailWord_278157).sum := by decide
  have hdescent : baseEnd_278157 < baseStart_278157 := by decide
  rcases family_descends (prefixWord ++ tailWord_278157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278212 : List Nat := [2, 3, 3, 1, 1, 1, 8]
def baseStart_278212 : Nat := 118140960795 + 278212 * 2 ^ 59
def prefixEnd_278212 : Nat := 4983230072969 + 3 ^ 40 * 278212 * 2
def baseEnd_278212 : Nat := 28218563920744835154673

theorem tailTrace_278212 : CollatzResearch.WordTrace tailWord_278212 prefixEnd_278212 28218563920744835154673 := by
  unfold tailWord_278212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073612634046456835930445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6764816845395275781240593 5073612634046456835930445)
  ·
    refine ⟨1902604737767421313473917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5073612634046456835930445 1902604737767421313473917)
    ·
      refine ⟨713476776662782992552719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1902604737767421313473917 713476776662782992552719)
      ·
        refine ⟨1070215164994174488829079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713476776662782992552719 1070215164994174488829079)
        ·
          refine ⟨1605322747491261733243619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070215164994174488829079 1605322747491261733243619)
          ·
            refine ⟨2407984121236892599865429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605322747491261733243619 2407984121236892599865429)
            ·
              refine ⟨28218563920744835154673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2407984121236892599865429 28218563920744835154673)
              ·
                rfl

theorem cell19_278212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_278212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278212 prefixEnd_278212 := by exact prefixLift 278212
  have htrace : WordTrace (prefixWord ++ tailWord_278212) baseStart_278212 baseEnd_278212 := by
    simpa [prefixWord, tailWord_278212, baseEnd_278212] using wordTrace_append hprefix tailTrace_278212
  have hstable : (prefixWord ++ tailWord_278212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278212).length < 2 ^ (prefixWord ++ tailWord_278212).sum := by decide
  have hdescent : baseEnd_278212 < baseStart_278212 := by decide
  rcases family_descends (prefixWord ++ tailWord_278212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278248 : List Nat := [2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_278248 : Nat := 118140960795 + 278248 * 2 ^ 59
def prefixEnd_278248 : Nat := 4983230072969 + 3 ^ 40 * 278248 * 2
def baseEnd_278248 : Nat := 84666646016197088663921

theorem tailTrace_278248 : CollatzResearch.WordTrace tailWord_278248 prefixEnd_278248 84666646016197088663921 := by
  unfold tailWord_278248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074269147981245910085699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6765692197308327880114265 5074269147981245910085699)
  ·
    refine ⟨7611403721971868865128549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5074269147981245910085699 7611403721971868865128549)
    ·
      refine ⟨1427138197869725412211603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7611403721971868865128549 1427138197869725412211603)
      ·
        refine ⟨2140707296804588118317405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1427138197869725412211603 2140707296804588118317405)
        ·
          refine ⟨802765236301720544369027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2140707296804588118317405 802765236301720544369027)
          ·
            refine ⟨1204147854452580816553541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802765236301720544369027 1204147854452580816553541)
            ·
              refine ⟨225777722709858903103789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1204147854452580816553541 225777722709858903103789)
              ·
                refine ⟨84666646016197088663921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225777722709858903103789 84666646016197088663921)
                ·
                  rfl

theorem cell19_278248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_278248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278248 prefixEnd_278248 := by exact prefixLift 278248
  have htrace : WordTrace (prefixWord ++ tailWord_278248) baseStart_278248 baseEnd_278248 := by
    simpa [prefixWord, tailWord_278248, baseEnd_278248] using wordTrace_append hprefix tailTrace_278248
  have hstable : (prefixWord ++ tailWord_278248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278248).length < 2 ^ (prefixWord ++ tailWord_278248).sum := by decide
  have hdescent : baseEnd_278248 < baseStart_278248 := by decide
  rcases family_descends (prefixWord ++ tailWord_278248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278271 : List Nat := [1, 1, 2, 2, 1, 3, 9]
def baseStart_278271 : Nat := 118140960795 + 278271 * 2 ^ 59
def prefixEnd_278271 : Nat := 4983230072969 + 3 ^ 40 * 278271 * 2
def baseEnd_278271 : Nat := 28224548189113283384249

theorem tailTrace_278271 : CollatzResearch.WordTrace tailWord_278271 prefixEnd_278271 28224548189113283384249 := by
  unfold tailWord_278271
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149377174879166748258667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6766251449919444498839111 10149377174879166748258667)
  ·
    refine ⟨15224065762318750122388001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10149377174879166748258667 15224065762318750122388001)
    ·
      refine ⟨11418049321739062591791001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15224065762318750122388001 11418049321739062591791001)
      ·
        refine ⟨8563536991304296943843251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11418049321739062591791001 8563536991304296943843251)
        ·
          refine ⟨12845305486956445415764877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8563536991304296943843251 12845305486956445415764877)
          ·
            refine ⟨4816989557608667030911829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12845305486956445415764877 4816989557608667030911829)
            ·
              refine ⟨28224548189113283384249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4816989557608667030911829 28224548189113283384249)
              ·
                rfl

theorem cell19_278271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_278271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278271 prefixEnd_278271 := by exact prefixLift 278271
  have htrace : WordTrace (prefixWord ++ tailWord_278271) baseStart_278271 baseEnd_278271 := by
    simpa [prefixWord, tailWord_278271, baseEnd_278271] using wordTrace_append hprefix tailTrace_278271
  have hstable : (prefixWord ++ tailWord_278271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278271).length < 2 ^ (prefixWord ++ tailWord_278271).sum := by decide
  have hdescent : baseEnd_278271 < baseStart_278271 := by decide
  rcases family_descends (prefixWord ++ tailWord_278271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278278 : List Nat := [6, 2, 2, 1, 1, 1, 2, 4]
def baseStart_278278 : Nat := 118140960795 + 278278 * 2 ^ 59
def prefixEnd_278278 : Nat := 4983230072969 + 3 ^ 40 * 278278 * 2
def baseEnd_278278 : Nat := 84675774561165907997173

theorem tailTrace_278278 : CollatzResearch.WordTrace tailWord_278278 prefixEnd_278278 84675774561165907997173 := by
  unfold tailWord_278278
  simp only [CollatzResearch.WordTrace]
  refine ⟨317176015182931466992609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6766421657235871295842325 317176015182931466992609)
  ·
    refine ⟨237882011387198600244457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 317176015182931466992609 237882011387198600244457)
    ·
      refine ⟨178411508540398950183343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237882011387198600244457 178411508540398950183343)
      ·
        refine ⟨267617262810598425275015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178411508540398950183343 267617262810598425275015)
        ·
          refine ⟨401425894215897637912523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267617262810598425275015 401425894215897637912523)
          ·
            refine ⟨602138841323846456868785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401425894215897637912523 602138841323846456868785)
            ·
              refine ⟨451604130992884842651589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602138841323846456868785 451604130992884842651589)
              ·
                refine ⟨84675774561165907997173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451604130992884842651589 84675774561165907997173)
                ·
                  rfl

theorem cell19_278278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_278278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278278 prefixEnd_278278 := by exact prefixLift 278278
  have htrace : WordTrace (prefixWord ++ tailWord_278278) baseStart_278278 baseEnd_278278 := by
    simpa [prefixWord, tailWord_278278, baseEnd_278278] using wordTrace_append hprefix tailTrace_278278
  have hstable : (prefixWord ++ tailWord_278278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278278).length < 2 ^ (prefixWord ++ tailWord_278278).sum := by decide
  have hdescent : baseEnd_278278 < baseStart_278278 := by decide
  rcases family_descends (prefixWord ++ tailWord_278278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278328 : List Nat := [2, 1, 2, 1, 3, 10]
def baseStart_278328 : Nat := 118140960795 + 278328 * 2 ^ 59
def prefixEnd_278328 : Nat := 4983230072969 + 3 ^ 40 * 278328 * 2
def baseEnd_278328 : Nat := 9410109866975622987325

theorem tailTrace_278328 : CollatzResearch.WordTrace tailWord_278328 prefixEnd_278328 9410109866975622987325 := by
  unfold tailWord_278328
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075728067836332741541819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6767637423781776988722425 5075728067836332741541819)
  ·
    refine ⟨7613592101754499112312729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5075728067836332741541819 7613592101754499112312729)
    ·
      refine ⟨5710194076315874334234547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7613592101754499112312729 5710194076315874334234547)
      ·
        refine ⟨8565291114473811501351821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710194076315874334234547 8565291114473811501351821)
        ·
          refine ⟨3211984167927679313006933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8565291114473811501351821 3211984167927679313006933)
          ·
            refine ⟨9410109866975622987325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3211984167927679313006933 9410109866975622987325)
            ·
              rfl

theorem cell19_278328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_278328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278328 prefixEnd_278328 := by exact prefixLift 278328
  have htrace : WordTrace (prefixWord ++ tailWord_278328) baseStart_278328 baseEnd_278328 := by
    simpa [prefixWord, tailWord_278328, baseEnd_278328] using wordTrace_append hprefix tailTrace_278328
  have hstable : (prefixWord ++ tailWord_278328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278328).length < 2 ^ (prefixWord ++ tailWord_278328).sum := by decide
  have hdescent : baseEnd_278328 < baseStart_278328 := by decide
  rcases family_descends (prefixWord ++ tailWord_278328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278385 : List Nat := [1, 2, 2, 2, 1, 3, 8]
def baseStart_278385 : Nat := 118140960795 + 278385 * 2 ^ 59
def prefixEnd_278385 : Nat := 4983230072969 + 3 ^ 40 * 278385 * 2
def baseEnd_278385 : Nat := 28236111012740454539701

theorem tailTrace_278385 : CollatzResearch.WordTrace tailWord_278385 prefixEnd_278385 28236111012740454539701 := by
  unfold tailWord_278385
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153535096466164217908609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6769023397644109478605739 10153535096466164217908609)
  ·
    refine ⟨7615151322349623163431457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10153535096466164217908609 7615151322349623163431457)
    ·
      refine ⟨5711363491762217372573593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7615151322349623163431457 5711363491762217372573593)
      ·
        refine ⟨4283522618821663029430195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5711363491762217372573593 4283522618821663029430195)
        ·
          refine ⟨6425283928232494544145293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283522618821663029430195 6425283928232494544145293)
          ·
            refine ⟨2409481473087185454054485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6425283928232494544145293 2409481473087185454054485)
            ·
              refine ⟨28236111012740454539701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2409481473087185454054485 28236111012740454539701)
              ·
                rfl

theorem cell19_278385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_278385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278385 prefixEnd_278385 := by exact prefixLift 278385
  have htrace : WordTrace (prefixWord ++ tailWord_278385) baseStart_278385 baseEnd_278385 := by
    simpa [prefixWord, tailWord_278385, baseEnd_278385] using wordTrace_append hprefix tailTrace_278385
  have hstable : (prefixWord ++ tailWord_278385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278385).length < 2 ^ (prefixWord ++ tailWord_278385).sum := by decide
  have hdescent : baseEnd_278385 < baseStart_278385 := by decide
  rcases family_descends (prefixWord ++ tailWord_278385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278480 : List Nat := [2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_278480 : Nat := 118140960795 + 278480 * 2 ^ 59
def prefixEnd_278480 : Nat := 4983230072969 + 3 ^ 40 * 278480 * 2
def baseEnd_278480 : Nat := 84737240097289291507733

theorem tailTrace_278480 : CollatzResearch.WordTrace tailWord_278480 prefixEnd_278480 84737240097289291507733 := by
  unfold tailWord_278480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078500015560997721308447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6771333354081330295077929 5078500015560997721308447)
  ·
    refine ⟨7617750023341496581962671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5078500015560997721308447 7617750023341496581962671)
    ·
      refine ⟨11426625035012244872944007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7617750023341496581962671 11426625035012244872944007)
      ·
        refine ⟨17139937552518367309416011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11426625035012244872944007 17139937552518367309416011)
        ·
          refine ⟨25709906328777550964124017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17139937552518367309416011 25709906328777550964124017)
          ·
            refine ⟨19282429746583163223093013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25709906328777550964124017 19282429746583163223093013)
            ·
              refine ⟨903863894371085776082485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19282429746583163223093013 903863894371085776082485)
              ·
                refine ⟨84737240097289291507733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 903863894371085776082485 84737240097289291507733)
                ·
                  rfl

theorem cell19_278480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_278480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278480 prefixEnd_278480 := by exact prefixLift 278480
  have htrace : WordTrace (prefixWord ++ tailWord_278480) baseStart_278480 baseEnd_278480 := by
    simpa [prefixWord, tailWord_278480, baseEnd_278480] using wordTrace_append hprefix tailTrace_278480
  have hstable : (prefixWord ++ tailWord_278480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278480).length < 2 ^ (prefixWord ++ tailWord_278480).sum := by decide
  have hdescent : baseEnd_278480 < baseStart_278480 := by decide
  rcases family_descends (prefixWord ++ tailWord_278480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278499 : List Nat := [1, 1, 1, 6, 1, 9]
def baseStart_278499 : Nat := 118140960795 + 278499 * 2 ^ 59
def prefixEnd_278499 : Nat := 4983230072969 + 3 ^ 40 * 278499 * 2
def baseEnd_278499 : Nat := 9415891278789208565051

theorem tailTrace_278499 : CollatzResearch.WordTrace tailWord_278499 prefixEnd_278499 9415891278789208565051 := by
  unfold tailWord_278499
  simp only [CollatzResearch.WordTrace]
  refine ⟨10157693018053161687558551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6771795345368774458372367 10157693018053161687558551)
  ·
    refine ⟨15236539527079742531337827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10157693018053161687558551 15236539527079742531337827)
    ·
      refine ⟨22854809290619613797006741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15236539527079742531337827 22854809290619613797006741)
      ·
        refine ⟨1071319185497794396734691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22854809290619613797006741 1071319185497794396734691)
        ·
          refine ⟨1606978778246691595102037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071319185497794396734691 1606978778246691595102037)
          ·
            refine ⟨9415891278789208565051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1606978778246691595102037 9415891278789208565051)
            ·
              rfl

theorem cell19_278499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_278499 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278499 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278499 prefixEnd_278499 := by exact prefixLift 278499
  have htrace : WordTrace (prefixWord ++ tailWord_278499) baseStart_278499 baseEnd_278499 := by
    simpa [prefixWord, tailWord_278499, baseEnd_278499] using wordTrace_append hprefix tailTrace_278499
  have hstable : (prefixWord ++ tailWord_278499).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278499).length < 2 ^ (prefixWord ++ tailWord_278499).sum := by decide
  have hdescent : baseEnd_278499 < baseStart_278499 := by decide
  rcases family_descends (prefixWord ++ tailWord_278499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278590 : List Nat := [4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_278590 : Nat := 118140960795 + 278590 * 2 ^ 59
def prefixEnd_278590 : Nat := 4983230072969 + 3 ^ 40 * 278590 * 2
def baseEnd_278590 : Nat := 84770711428841629062989

theorem tailTrace_278590 : CollatzResearch.WordTrace tailWord_278590 prefixEnd_278590 84770711428841629062989 := by
  unfold tailWord_278590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270126507590435528640153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6774008040482322819414149 1270126507590435528640153)
  ·
    refine ⟨952594880692826646480115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1270126507590435528640153 952594880692826646480115)
    ·
      refine ⟨1428892321039239969720173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952594880692826646480115 1428892321039239969720173)
      ·
        refine ⟨535834620389714988645065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1428892321039239969720173 535834620389714988645065)
        ·
          refine ⟨401875965292286241483799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535834620389714988645065 401875965292286241483799)
          ·
            refine ⟨602813947938429362225699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401875965292286241483799 602813947938429362225699)
            ·
              refine ⟨904220921907644043338549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602813947938429362225699 904220921907644043338549)
              ·
                refine ⟨84770711428841629062989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 904220921907644043338549 84770711428841629062989)
                ·
                  rfl

theorem cell19_278590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_278590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278590 prefixEnd_278590 := by exact prefixLift 278590
  have htrace : WordTrace (prefixWord ++ tailWord_278590) baseStart_278590 baseEnd_278590 := by
    simpa [prefixWord, tailWord_278590, baseEnd_278590] using wordTrace_append hprefix tailTrace_278590
  have hstable : (prefixWord ++ tailWord_278590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278590).length < 2 ^ (prefixWord ++ tailWord_278590).sum := by decide
  have hdescent : baseEnd_278590 < baseStart_278590 := by decide
  rcases family_descends (prefixWord ++ tailWord_278590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278592 : List Nat := [2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_278592 : Nat := 118140960795 + 278592 * 2 ^ 59
def prefixEnd_278592 : Nat := 4983230072969 + 3 ^ 40 * 278592 * 2
def baseEnd_278592 : Nat := 84771319998506217018539

theorem tailTrace_278592 : CollatzResearch.WordTrace tailWord_278592 prefixEnd_278592 84771319998506217018539 := by
  unfold tailWord_278592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080542503358119285347015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6774056671144159047129353 5080542503358119285347015)
  ·
    refine ⟨7620813755037178928020523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5080542503358119285347015 7620813755037178928020523)
    ·
      refine ⟨11431220632555768392030785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7620813755037178928020523 11431220632555768392030785)
      ·
        refine ⟨8573415474416826294023089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11431220632555768392030785 8573415474416826294023089)
        ·
          refine ⟨6430061605812619720517317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8573415474416826294023089 6430061605812619720517317)
          ·
            refine ⟨1205636551089866197596997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6430061605812619720517317 1205636551089866197596997)
            ·
              refine ⟨226056853329349912049437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1205636551089866197596997 226056853329349912049437)
              ·
                refine ⟨84771319998506217018539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226056853329349912049437 84771319998506217018539)
                ·
                  rfl

theorem cell19_278592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_278592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278592 prefixEnd_278592 := by exact prefixLift 278592
  have htrace : WordTrace (prefixWord ++ tailWord_278592) baseStart_278592 baseEnd_278592 := by
    simpa [prefixWord, tailWord_278592, baseEnd_278592] using wordTrace_append hprefix tailTrace_278592
  have hstable : (prefixWord ++ tailWord_278592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278592).length < 2 ^ (prefixWord ++ tailWord_278592).sum := by decide
  have hdescent : baseEnd_278592 < baseStart_278592 := by decide
  rcases family_descends (prefixWord ++ tailWord_278592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278613 : List Nat := [1, 3, 2, 2, 1, 3, 7]
def baseStart_278613 : Nat := 118140960795 + 278613 * 2 ^ 59
def prefixEnd_278613 : Nat := 4983230072969 + 3 ^ 40 * 278613 * 2
def baseEnd_278613 : Nat := 28259236659994796850605

theorem tailTrace_278613 : CollatzResearch.WordTrace tailWord_278613 prefixEnd_278613 28259236659994796850605 := by
  unfold tailWord_278613
  simp only [CollatzResearch.WordTrace]
  refine ⟨10161850939640159157208493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6774567293093439438138995 10161850939640159157208493)
  ·
    refine ⟨3810694102365059683953185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10161850939640159157208493 3810694102365059683953185)
    ·
      refine ⟨2858020576773794762964889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3810694102365059683953185 2858020576773794762964889)
      ·
        refine ⟨2143515432580346072223667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2858020576773794762964889 2143515432580346072223667)
        ·
          refine ⟨3215273148870519108335501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143515432580346072223667 3215273148870519108335501)
          ·
            refine ⟨1205727430826444665625813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3215273148870519108335501 1205727430826444665625813)
            ·
              refine ⟨28259236659994796850605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1205727430826444665625813 28259236659994796850605)
              ·
                rfl

theorem cell19_278613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_278613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278613 prefixEnd_278613 := by exact prefixLift 278613
  have htrace : WordTrace (prefixWord ++ tailWord_278613) baseStart_278613 baseEnd_278613 := by
    simpa [prefixWord, tailWord_278613, baseEnd_278613] using wordTrace_append hprefix tailTrace_278613
  have hstable : (prefixWord ++ tailWord_278613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278613).length < 2 ^ (prefixWord ++ tailWord_278613).sum := by decide
  have hdescent : baseEnd_278613 < baseStart_278613 := by decide
  rcases family_descends (prefixWord ++ tailWord_278613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278670 : List Nat := [4, 1, 1, 3, 10]
def baseStart_278670 : Nat := 118140960795 + 278670 * 2 ^ 59
def prefixEnd_278670 : Nat := 4983230072969 + 3 ^ 40 * 278670 * 2
def baseEnd_278670 : Nat := 3140557563534264714259

theorem tailTrace_278670 : CollatzResearch.WordTrace tailWord_278670 prefixEnd_278670 3140557563534264714259 := by
  unfold tailWord_278670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270491237554207236504183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6775953266955771928022309 1270491237554207236504183)
  ·
    refine ⟨1905736856331310854756275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1270491237554207236504183 1905736856331310854756275)
    ·
      refine ⟨2858605284496966282134413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905736856331310854756275 2858605284496966282134413)
      ·
        refine ⟨1071976981686362355800405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2858605284496966282134413 1071976981686362355800405)
        ·
          refine ⟨3140557563534264714259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1071976981686362355800405 3140557563534264714259)
          ·
            rfl

theorem cell19_278670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 10].length) (baseStart_278670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278670 prefixEnd_278670 := by exact prefixLift 278670
  have htrace : WordTrace (prefixWord ++ tailWord_278670) baseStart_278670 baseEnd_278670 := by
    simpa [prefixWord, tailWord_278670, baseEnd_278670] using wordTrace_append hprefix tailTrace_278670
  have hstable : (prefixWord ++ tailWord_278670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278670).length < 2 ^ (prefixWord ++ tailWord_278670).sum := by decide
  have hdescent : baseEnd_278670 < baseStart_278670 := by decide
  rcases family_descends (prefixWord ++ tailWord_278670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278687 : List Nat := [1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_278687 : Nat := 118140960795 + 278687 * 2 ^ 59
def prefixEnd_278687 : Nat := 4983230072969 + 3 ^ 40 * 278687 * 2
def baseEnd_278687 : Nat := 84800227057574144907169

theorem tailTrace_278687 : CollatzResearch.WordTrace tailWord_278687 prefixEnd_278687 84800227057574144907169 := by
  unfold tailWord_278687
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164549941372069795402315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6776366627581379863601543 10164549941372069795402315)
  ·
    refine ⟨15246824912058104693103473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10164549941372069795402315 15246824912058104693103473)
    ·
      refine ⟨11435118684043578519827605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15246824912058104693103473 11435118684043578519827605)
      ·
        refine ⟨536021188314542743116919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11435118684043578519827605 536021188314542743116919)
        ·
          refine ⟨804031782471814114675379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536021188314542743116919 804031782471814114675379)
          ·
            refine ⟨1206047673707721172013069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804031782471814114675379 1206047673707721172013069)
            ·
              refine ⟨452267877640395439504901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1206047673707721172013069 452267877640395439504901)
              ·
                refine ⟨84800227057574144907169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452267877640395439504901 84800227057574144907169)
                ·
                  rfl

theorem cell19_278687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_278687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278687 prefixEnd_278687 := by exact prefixLift 278687
  have htrace : WordTrace (prefixWord ++ tailWord_278687) baseStart_278687 baseEnd_278687 := by
    simpa [prefixWord, tailWord_278687, baseEnd_278687] using wordTrace_append hprefix tailTrace_278687
  have hstable : (prefixWord ++ tailWord_278687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278687).length < 2 ^ (prefixWord ++ tailWord_278687).sum := by decide
  have hdescent : baseEnd_278687 < baseStart_278687 := by decide
  rcases family_descends (prefixWord ++ tailWord_278687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278706 : List Nat := [3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_278706 : Nat := 118140960795 + 278706 * 2 ^ 59
def prefixEnd_278706 : Nat := 4983230072969 + 3 ^ 40 * 278706 * 2
def baseEnd_278706 : Nat := 84806008469387730484895

theorem tailTrace_278706 : CollatzResearch.WordTrace tailWord_278706 prefixEnd_278706 84806008469387730484895 := by
  unfold tailWord_278706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541310732075809010085993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6776828618868824026895981 2541310732075809010085993)
  ·
    refine ⟨1905983049056856757564495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2541310732075809010085993 1905983049056856757564495)
    ·
      refine ⟨2858974573585285136346743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905983049056856757564495 2858974573585285136346743)
      ·
        refine ⟨4288461860377927704520115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858974573585285136346743 4288461860377927704520115)
        ·
          refine ⟨6432692790566891556780173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288461860377927704520115 6432692790566891556780173)
          ·
            refine ⟨2412259796462584333792565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6432692790566891556780173 2412259796462584333792565)
            ·
              refine ⟨226149355918367281293053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2412259796462584333792565 226149355918367281293053)
              ·
                refine ⟨84806008469387730484895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226149355918367281293053 84806008469387730484895)
                ·
                  rfl

theorem cell19_278706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_278706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278706 prefixEnd_278706 := by exact prefixLift 278706
  have htrace : WordTrace (prefixWord ++ tailWord_278706) baseStart_278706 baseEnd_278706 := by
    simpa [prefixWord, tailWord_278706, baseEnd_278706] using wordTrace_append hprefix tailTrace_278706
  have hstable : (prefixWord ++ tailWord_278706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278706).length < 2 ^ (prefixWord ++ tailWord_278706).sum := by decide
  have hdescent : baseEnd_278706 < baseStart_278706 := by decide
  rcases family_descends (prefixWord ++ tailWord_278706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278841 : List Nat := [1, 2, 1, 6, 1, 8]
def baseStart_278841 : Nat := 118140960795 + 278841 * 2 ^ 59
def prefixEnd_278841 : Nat := 4983230072969 + 3 ^ 40 * 278841 * 2
def baseEnd_278841 : Nat := 9427454102416379720503

theorem tailTrace_278841 : CollatzResearch.WordTrace tailWord_278841 prefixEnd_278841 9427454102416379720503 := by
  unfold tailWord_278841
  simp only [CollatzResearch.WordTrace]
  refine ⟨10170166782814154096508377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6780111188542769397672251 10170166782814154096508377)
  ·
    refine ⟨7627625087110615572381283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10170166782814154096508377 7627625087110615572381283)
    ·
      refine ⟨11441437630665923358571925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7627625087110615572381283 11441437630665923358571925)
      ·
        refine ⟨536317388937465157433059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11441437630665923358571925 536317388937465157433059)
        ·
          refine ⟨804476083406197736149589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536317388937465157433059 804476083406197736149589)
          ·
            refine ⟨9427454102416379720503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 804476083406197736149589 9427454102416379720503)
            ·
              rfl

theorem cell19_278841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_278841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278841 prefixEnd_278841 := by exact prefixLift 278841
  have htrace : WordTrace (prefixWord ++ tailWord_278841) baseStart_278841 baseEnd_278841 := by
    simpa [prefixWord, tailWord_278841, baseEnd_278841] using wordTrace_append hprefix tailTrace_278841
  have hstable : (prefixWord ++ tailWord_278841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278841).length < 2 ^ (prefixWord ++ tailWord_278841).sum := by decide
  have hdescent : baseEnd_278841 < baseStart_278841 := by decide
  rcases family_descends (prefixWord ++ tailWord_278841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278898 : List Nat := [3, 2, 1, 2, 1, 4, 6]
def baseStart_278898 : Nat := 118140960795 + 278898 * 2 ^ 59
def prefixEnd_278898 : Nat := 4983230072969 + 3 ^ 40 * 278898 * 2
def baseEnd_278898 : Nat := 28288143719062724739235

theorem tailTrace_278898 : CollatzResearch.WordTrace tailWord_278898 prefixEnd_278898 28288143719062724739235 := by
  unfold tailWord_278898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543061435901913207833337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6781497162405101887555565 2543061435901913207833337)
  ·
    refine ⟨1907296076926434905875003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2543061435901913207833337 1907296076926434905875003)
    ·
      refine ⟨2860944115389652358812505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907296076926434905875003 2860944115389652358812505)
      ·
        refine ⟨2145708086542239269109379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2860944115389652358812505 2145708086542239269109379)
        ·
          refine ⟨3218562129813358903664069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145708086542239269109379 3218562129813358903664069)
          ·
            refine ⟨603480399340004794437013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3218562129813358903664069 603480399340004794437013)
            ·
              refine ⟨28288143719062724739235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 603480399340004794437013 28288143719062724739235)
              ·
                rfl

theorem cell19_278898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_278898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278898 prefixEnd_278898 := by exact prefixLift 278898
  have htrace : WordTrace (prefixWord ++ tailWord_278898) baseStart_278898 baseEnd_278898 := by
    simpa [prefixWord, tailWord_278898, baseEnd_278898] using wordTrace_append hprefix tailTrace_278898
  have hstable : (prefixWord ++ tailWord_278898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278898).length < 2 ^ (prefixWord ++ tailWord_278898).sum := by decide
  have hdescent : baseEnd_278898 < baseStart_278898 := by decide
  rcases family_descends (prefixWord ++ tailWord_278898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278972 : List Nat := [2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_278972 : Nat := 118140960795 + 278972 * 2 ^ 59
def prefixEnd_278972 : Nat := 4983230072969 + 3 ^ 40 * 278972 * 2
def baseEnd_278972 : Nat := 84886948234777928573059

theorem tailTrace_278972 : CollatzResearch.WordTrace tailWord_278972 prefixEnd_278972 84886948234777928573059 := by
  unfold tailWord_278972
  simp only [CollatzResearch.WordTrace]
  refine ⟨5087472372669781734763585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6783296496893042313018113 5087472372669781734763585)
  ·
    refine ⟨3815604279502336301072689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5087472372669781734763585 3815604279502336301072689)
    ·
      refine ⟨2861703209626752225804517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3815604279502336301072689 2861703209626752225804517)
      ·
        refine ⟨536569351805016042338347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2861703209626752225804517 536569351805016042338347)
        ·
          refine ⟨804854027707524063507521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536569351805016042338347 804854027707524063507521)
          ·
            refine ⟨603640520780643047630641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804854027707524063507521 603640520780643047630641)
            ·
              refine ⟨452730390585482285722981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603640520780643047630641 452730390585482285722981)
              ·
                refine ⟨84886948234777928573059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452730390585482285722981 84886948234777928573059)
                ·
                  rfl

theorem cell19_278972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_278972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278972 prefixEnd_278972 := by exact prefixLift 278972
  have htrace : WordTrace (prefixWord ++ tailWord_278972) baseStart_278972 baseEnd_278972 := by
    simpa [prefixWord, tailWord_278972, baseEnd_278972] using wordTrace_append hprefix tailTrace_278972
  have hstable : (prefixWord ++ tailWord_278972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278972).length < 2 ^ (prefixWord ++ tailWord_278972).sum := by decide
  have hdescent : baseEnd_278972 < baseStart_278972 := by decide
  rcases family_descends (prefixWord ++ tailWord_278972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278974 : List Nat := [4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_278974 : Nat := 118140960795 + 278974 * 2 ^ 59
def prefixEnd_278974 : Nat := 4983230072969 + 3 ^ 40 * 278974 * 2
def baseEnd_278974 : Nat := 84887556804442516528609

theorem tailTrace_278974 : CollatzResearch.WordTrace tailWord_278974 prefixEnd_278974 84887556804442516528609 := by
  unfold tailWord_278974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271877211416539726387497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6783345127554878540733317 1271877211416539726387497)
  ·
    refine ⟨953907908562404794790623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1271877211416539726387497 953907908562404794790623)
    ·
      refine ⟨1430861862843607192185935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953907908562404794790623 1430861862843607192185935)
      ·
        refine ⟨2146292794265410788278903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430861862843607192185935 2146292794265410788278903)
        ·
          refine ⟨3219439191398116182418355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146292794265410788278903 3219439191398116182418355)
          ·
            refine ⟨4829158787097174273627533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219439191398116182418355 4829158787097174273627533)
            ·
              refine ⟨1810934545161440352610325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4829158787097174273627533 1810934545161440352610325)
              ·
                refine ⟨84887556804442516528609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1810934545161440352610325 84887556804442516528609)
                ·
                  rfl

theorem cell19_278974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_278974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_278974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_278974 prefixEnd_278974 := by exact prefixLift 278974
  have htrace : WordTrace (prefixWord ++ tailWord_278974) baseStart_278974 baseEnd_278974 := by
    simpa [prefixWord, tailWord_278974, baseEnd_278974] using wordTrace_append hprefix tailTrace_278974
  have hstable : (prefixWord ++ tailWord_278974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278974).length < 2 ^ (prefixWord ++ tailWord_278974).sum := by decide
  have hdescent : baseEnd_278974 < baseStart_278974 := by decide
  rcases family_descends (prefixWord ++ tailWord_278974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279010 : List Nat := [3, 3, 3, 2, 8]
def baseStart_279010 : Nat := 118140960795 + 279010 * 2 ^ 59
def prefixEnd_279010 : Nat := 4983230072969 + 3 ^ 40 * 279010 * 2
def baseEnd_279010 : Nat := 3144389298459448138093

theorem tailTrace_279010 : CollatzResearch.WordTrace tailWord_279010 prefixEnd_279010 3144389298459448138093 := by
  unfold tailWord_279010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2544082679800473989852621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6784220479467930639606989 2544082679800473989852621)
  ·
    refine ⟨954031004925177746194733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2544082679800473989852621 954031004925177746194733)
    ·
      refine ⟨357761626846941654823025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 954031004925177746194733 357761626846941654823025)
      ·
        refine ⟨268321220135206241117269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357761626846941654823025 268321220135206241117269)
        ·
          refine ⟨3144389298459448138093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 268321220135206241117269 3144389298459448138093)
          ·
            rfl

theorem cell19_279010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 8].length) (baseStart_279010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279010 prefixEnd_279010 := by exact prefixLift 279010
  have htrace : WordTrace (prefixWord ++ tailWord_279010) baseStart_279010 baseEnd_279010 := by
    simpa [prefixWord, tailWord_279010, baseEnd_279010] using wordTrace_append hprefix tailTrace_279010
  have hstable : (prefixWord ++ tailWord_279010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279010).length < 2 ^ (prefixWord ++ tailWord_279010).sum := by decide
  have hdescent : baseEnd_279010 < baseStart_279010 := by decide
  rcases family_descends (prefixWord ++ tailWord_279010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279069 : List Nat := [1, 4, 2, 2, 1, 3, 6]
def baseStart_279069 : Nat := 118140960795 + 279069 * 2 ^ 59
def prefixEnd_279069 : Nat := 4983230072969 + 3 ^ 40 * 279069 * 2
def baseEnd_279069 : Nat := 28305487954503481472413

theorem tailTrace_279069 : CollatzResearch.WordTrace tailWord_279069 prefixEnd_279069 28305487954503481472413 := by
  unfold tailWord_279069
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178482625988149035808261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6785655083992099357205507 10178482625988149035808261)
  ·
    refine ⟨1908465492372777944214049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10178482625988149035808261 1908465492372777944214049)
    ·
      refine ⟨1431349119279583458160537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1908465492372777944214049 1431349119279583458160537)
      ·
        refine ⟨1073511839459687593620403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1431349119279583458160537 1073511839459687593620403)
        ·
          refine ⟨1610267759189531390430605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073511839459687593620403 1610267759189531390430605)
          ·
            refine ⟨603850409696074271411477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1610267759189531390430605 603850409696074271411477)
            ·
              refine ⟨28305487954503481472413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 603850409696074271411477 28305487954503481472413)
              ·
                rfl

theorem cell19_279069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_279069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279069 prefixEnd_279069 := by exact prefixLift 279069
  have htrace : WordTrace (prefixWord ++ tailWord_279069) baseStart_279069 baseEnd_279069 := by
    simpa [prefixWord, tailWord_279069, baseEnd_279069] using wordTrace_append hprefix tailTrace_279069
  have hstable : (prefixWord ++ tailWord_279069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279069).length < 2 ^ (prefixWord ++ tailWord_279069).sum := by decide
  have hdescent : baseEnd_279069 < baseStart_279069 := by decide
  rcases family_descends (prefixWord ++ tailWord_279069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279105 : List Nat := [1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_279105 : Nat := 118140960795 + 279105 * 2 ^ 59
def prefixEnd_279105 : Nat := 4983230072969 + 3 ^ 40 * 279105 * 2
def baseEnd_279105 : Nat := 84927418117473027617141

theorem tailTrace_279105 : CollatzResearch.WordTrace tailWord_279105 prefixEnd_279105 84927418117473027617141 := by
  unfold tailWord_279105
  simp only [CollatzResearch.WordTrace]
  refine ⟨10179795653857727184118769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6786530435905151456079179 10179795653857727184118769)
  ·
    refine ⟨7634846740393295388089077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10179795653857727184118769 7634846740393295388089077)
    ·
      refine ⟨715766881911871442633351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7634846740393295388089077 715766881911871442633351)
      ·
        refine ⟨1073650322867807163950027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715766881911871442633351 1073650322867807163950027)
        ·
          refine ⟨1610475484301710745925041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073650322867807163950027 1610475484301710745925041)
          ·
            refine ⟨1207856613226283059443781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610475484301710745925041 1207856613226283059443781)
            ·
              refine ⟨226473114979928073645709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1207856613226283059443781 226473114979928073645709)
              ·
                refine ⟨84927418117473027617141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226473114979928073645709 84927418117473027617141)
                ·
                  rfl

theorem cell19_279105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_279105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279105 prefixEnd_279105 := by exact prefixLift 279105
  have htrace : WordTrace (prefixWord ++ tailWord_279105) baseStart_279105 baseEnd_279105 := by
    simpa [prefixWord, tailWord_279105, baseEnd_279105] using wordTrace_append hprefix tailTrace_279105
  have hstable : (prefixWord ++ tailWord_279105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279105).length < 2 ^ (prefixWord ++ tailWord_279105).sum := by decide
  have hdescent : baseEnd_279105 < baseStart_279105 := by decide
  rcases family_descends (prefixWord ++ tailWord_279105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279128 : List Nat := [2, 1, 2, 2, 1, 2, 9]
def baseStart_279128 : Nat := 118140960795 + 279128 * 2 ^ 59
def prefixEnd_279128 : Nat := 4983230072969 + 3 ^ 40 * 279128 * 2
def baseEnd_279128 : Nat := 28311472222871929701989

theorem tailTrace_279128 : CollatzResearch.WordTrace tailWord_279128 prefixEnd_279128 28311472222871929701989 := by
  unfold tailWord_279128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090317266387201056103019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6787089688516268074804025 5090317266387201056103019)
  ·
    refine ⟨7635475899580801584154529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5090317266387201056103019 7635475899580801584154529)
    ·
      refine ⟨5726606924685601188115897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7635475899580801584154529 5726606924685601188115897)
      ·
        refine ⟨4294955193514200891086923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5726606924685601188115897 4294955193514200891086923)
        ·
          refine ⟨6442432790271301336630385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294955193514200891086923 6442432790271301336630385)
          ·
            refine ⟨4831824592703476002472789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6442432790271301336630385 4831824592703476002472789)
            ·
              refine ⟨28311472222871929701989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4831824592703476002472789 28311472222871929701989)
              ·
                rfl

theorem cell19_279128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_279128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279128 prefixEnd_279128 := by exact prefixLift 279128
  have htrace : WordTrace (prefixWord ++ tailWord_279128) baseStart_279128 baseEnd_279128 := by
    simpa [prefixWord, tailWord_279128, baseEnd_279128] using wordTrace_append hprefix tailTrace_279128
  have hstable : (prefixWord ++ tailWord_279128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279128).length < 2 ^ (prefixWord ++ tailWord_279128).sum := by decide
  have hdescent : baseEnd_279128 < baseStart_279128 := by decide
  rcases family_descends (prefixWord ++ tailWord_279128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279200 : List Nat := [2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_279200 : Nat := 118140960795 + 279200 * 2 ^ 59
def prefixEnd_279200 : Nat := 4983230072969 + 3 ^ 40 * 279200 * 2
def baseEnd_279200 : Nat := 84956325176540955505771

theorem tailTrace_279200 : CollatzResearch.WordTrace tailWord_279200 prefixEnd_279200 84956325176540955505771 := by
  unfold tailWord_279200
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091630294256779204413527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6788840392342372272551369 5091630294256779204413527)
  ·
    refine ⟨7637445441385168806620291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091630294256779204413527 7637445441385168806620291)
    ·
      refine ⟨11456168162077753209930437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7637445441385168806620291 11456168162077753209930437)
      ·
        refine ⟨2148031530389578726861957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11456168162077753209930437 2148031530389578726861957)
        ·
          refine ⟨402755911948046011286617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2148031530389578726861957 402755911948046011286617)
          ·
            refine ⟨302066933961034508464963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402755911948046011286617 302066933961034508464963)
            ·
              refine ⟨453100400941551762697445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302066933961034508464963 453100400941551762697445)
              ·
                refine ⟨84956325176540955505771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453100400941551762697445 84956325176540955505771)
                ·
                  rfl

theorem cell19_279200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_279200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279200 prefixEnd_279200 := by exact prefixLift 279200
  have htrace : WordTrace (prefixWord ++ tailWord_279200) baseStart_279200 baseEnd_279200 := by
    simpa [prefixWord, tailWord_279200, baseEnd_279200] using wordTrace_append hprefix tailTrace_279200
  have hstable : (prefixWord ++ tailWord_279200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279200).length < 2 ^ (prefixWord ++ tailWord_279200).sum := by decide
  have hdescent : baseEnd_279200 < baseStart_279200 := by decide
  rcases family_descends (prefixWord ++ tailWord_279200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279217 : List Nat := [1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_279217 : Nat := 118140960795 + 279217 * 2 ^ 59
def prefixEnd_279217 : Nat := 4983230072969 + 3 ^ 40 * 279217 * 2
def baseEnd_279217 : Nat := 84961498018689953127947

theorem tailTrace_279217 : CollatzResearch.WordTrace tailWord_279217 prefixEnd_279217 84961498018689953127947 := by
  unfold tailWord_279217
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183880629451970312195905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6789253752967980208130603 10183880629451970312195905)
  ·
    refine ⟨7637910472088977734146929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10183880629451970312195905 7637910472088977734146929)
    ·
      refine ⟨5728432854066733300610197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7637910472088977734146929 5728432854066733300610197)
      ·
        refine ⟨268520290034378123466103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5728432854066733300610197 268520290034378123466103)
        ·
          refine ⟨402780435051567185199155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268520290034378123466103 402780435051567185199155)
          ·
            refine ⟨604170652577350777798733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402780435051567185199155 604170652577350777798733)
            ·
              refine ⟨226563994716506541674525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 604170652577350777798733 226563994716506541674525)
              ·
                refine ⟨84961498018689953127947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226563994716506541674525 84961498018689953127947)
                ·
                  rfl

theorem cell19_279217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_279217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279217 prefixEnd_279217 := by exact prefixLift 279217
  have htrace : WordTrace (prefixWord ++ tailWord_279217) baseStart_279217 baseEnd_279217 := by
    simpa [prefixWord, tailWord_279217, baseEnd_279217] using wordTrace_append hprefix tailTrace_279217
  have hstable : (prefixWord ++ tailWord_279217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279217).length < 2 ^ (prefixWord ++ tailWord_279217).sum := by decide
  have hdescent : baseEnd_279217 < baseStart_279217 := by decide
  rcases family_descends (prefixWord ++ tailWord_279217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279278 : List Nat := [4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_279278 : Nat := 118140960795 + 279278 * 2 ^ 59
def prefixEnd_279278 : Nat := 4983230072969 + 3 ^ 40 * 279278 * 2
def baseEnd_279278 : Nat := 84980059393459885772225

theorem tailTrace_279278 : CollatzResearch.WordTrace tailWord_279278 prefixEnd_279278 84980059393459885772225 := by
  unfold tailWord_279278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273263185278872216270811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6790736988153985153444325 1273263185278872216270811)
  ·
    refine ⟨1909894777918308324406217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1273263185278872216270811 1909894777918308324406217)
    ·
      refine ⟨1432421083438731243304663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1909894777918308324406217 1432421083438731243304663)
      ·
        refine ⟨2148631625158096864956995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432421083438731243304663 2148631625158096864956995)
        ·
          refine ⟨3222947437737145297435493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148631625158096864956995 3222947437737145297435493)
          ·
            refine ⟨604302644575714743269155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3222947437737145297435493 604302644575714743269155)
            ·
              refine ⟨906453966863572114903733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604302644575714743269155 906453966863572114903733)
              ·
                refine ⟨84980059393459885772225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 906453966863572114903733 84980059393459885772225)
                ·
                  rfl

theorem cell19_279278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_279278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279278 prefixEnd_279278 := by exact prefixLift 279278
  have htrace : WordTrace (prefixWord ++ tailWord_279278) baseStart_279278 baseEnd_279278 := by
    simpa [prefixWord, tailWord_279278, baseEnd_279278] using wordTrace_append hprefix tailTrace_279278
  have hstable : (prefixWord ++ tailWord_279278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279278).length < 2 ^ (prefixWord ++ tailWord_279278).sum := by decide
  have hdescent : baseEnd_279278 < baseStart_279278 := by decide
  rcases family_descends (prefixWord ++ tailWord_279278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279280 : List Nat := [2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_279280 : Nat := 118140960795 + 279280 * 2 ^ 59
def prefixEnd_279280 : Nat := 4983230072969 + 3 ^ 40 * 279280 * 2
def baseEnd_279280 : Nat := 84980667963124473727775

theorem tailTrace_279280 : CollatzResearch.WordTrace tailWord_279280 prefixEnd_279280 84980667963124473727775 := by
  unfold tailWord_279280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5093089214111866035869647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6790785618815821381159529 5093089214111866035869647)
  ·
    refine ⟨7639633821167799053804471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5093089214111866035869647 7639633821167799053804471)
    ·
      refine ⟨11459450731751698580706707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7639633821167799053804471 11459450731751698580706707)
      ·
        refine ⟨17189176097627547871060061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11459450731751698580706707 17189176097627547871060061)
        ·
          refine ⟨6445941036610330451647523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17189176097627547871060061 6445941036610330451647523)
          ·
            refine ⟨9668911554915495677471285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445941036610330451647523 9668911554915495677471285)
            ·
              refine ⟨906460458273327719762933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9668911554915495677471285 906460458273327719762933)
              ·
                refine ⟨84980667963124473727775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 906460458273327719762933 84980667963124473727775)
                ·
                  rfl

theorem cell19_279280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_279280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279280 prefixEnd_279280 := by exact prefixLift 279280
  have htrace : WordTrace (prefixWord ++ tailWord_279280) baseStart_279280 baseEnd_279280 := by
    simpa [prefixWord, tailWord_279280, baseEnd_279280] using wordTrace_append hprefix tailTrace_279280
  have hstable : (prefixWord ++ tailWord_279280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279280).length < 2 ^ (prefixWord ++ tailWord_279280).sum := by decide
  have hdescent : baseEnd_279280 < baseStart_279280 := by decide
  rcases family_descends (prefixWord ++ tailWord_279280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279354 : List Nat := [3, 1, 1, 1, 7, 6]
def baseStart_279354 : Nat := 118140960795 + 279354 * 2 ^ 59
def prefixEnd_279354 : Nat := 4983230072969 + 3 ^ 40 * 279354 * 2
def baseEnd_279354 : Nat := 9444798337857136453681

theorem tailTrace_279354 : CollatzResearch.WordTrace tailWord_279354 prefixEnd_279354 9444798337857136453681 := by
  unfold tailWord_279354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547219357488910677483279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6792584953303761806622077 2547219357488910677483279)
  ·
    refine ⟨3820829036233366016224919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547219357488910677483279 3820829036233366016224919)
    ·
      refine ⟨5731243554350049024337379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820829036233366016224919 5731243554350049024337379)
      ·
        refine ⟨8596865331525073536506069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5731243554350049024337379 8596865331525073536506069)
        ·
          refine ⟨201489031207618911011861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8596865331525073536506069 201489031207618911011861)
          ·
            refine ⟨9444798337857136453681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 201489031207618911011861 9444798337857136453681)
            ·
              rfl

theorem cell19_279354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_279354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279354 prefixEnd_279354 := by exact prefixLift 279354
  have htrace : WordTrace (prefixWord ++ tailWord_279354) baseStart_279354 baseEnd_279354 := by
    simpa [prefixWord, tailWord_279354, baseEnd_279354] using wordTrace_append hprefix tailTrace_279354
  have hstable : (prefixWord ++ tailWord_279354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279354).length < 2 ^ (prefixWord ++ tailWord_279354).sum := by decide
  have hdescent : baseEnd_279354 < baseStart_279354 := by decide
  rcases family_descends (prefixWord ++ tailWord_279354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279392 : List Nat := [2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_279392 : Nat := 118140960795 + 279392 * 2 ^ 59
def prefixEnd_279392 : Nat := 4983230072969 + 3 ^ 40 * 279392 * 2
def baseEnd_279392 : Nat := 85014747864341399238581

theorem tailTrace_279392 : CollatzResearch.WordTrace tailWord_279392 prefixEnd_279392 85014747864341399238581 := by
  unfold tailWord_279392
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095131701908987599908215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6793508935878650133210953 5095131701908987599908215)
  ·
    refine ⟨7642697552863481399862323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5095131701908987599908215 7642697552863481399862323)
    ·
      refine ⟨11464046329295222099793485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7642697552863481399862323 11464046329295222099793485)
      ·
        refine ⟨4299017373485708287422557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11464046329295222099793485 4299017373485708287422557)
        ·
          refine ⟨1612131515057140607783459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4299017373485708287422557 1612131515057140607783459)
          ·
            refine ⟨2418197272585710911675189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612131515057140607783459 2418197272585710911675189)
            ·
              refine ⟨226705994304910397969549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2418197272585710911675189 226705994304910397969549)
              ·
                refine ⟨85014747864341399238581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226705994304910397969549 85014747864341399238581)
                ·
                  rfl

theorem cell19_279392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_279392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279392 prefixEnd_279392 := by exact prefixLift 279392
  have htrace : WordTrace (prefixWord ++ tailWord_279392) baseStart_279392 baseEnd_279392 := by
    simpa [prefixWord, tailWord_279392, baseEnd_279392] using wordTrace_append hprefix tailTrace_279392
  have hstable : (prefixWord ++ tailWord_279392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279392).length < 2 ^ (prefixWord ++ tailWord_279392).sum := by decide
  have hdescent : baseEnd_279392 < baseStart_279392 := by decide
  rcases family_descends (prefixWord ++ tailWord_279392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279506 : List Nat := [3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_279506 : Nat := 118140960795 + 279506 * 2 ^ 59
def prefixEnd_279506 : Nat := 4983230072969 + 3 ^ 40 * 279506 * 2
def baseEnd_279506 : Nat := 85049436335222912704937

theorem tailTrace_279506 : CollatzResearch.WordTrace tailWord_279506 prefixEnd_279506 85049436335222912704937 := by
  unfold tailWord_279506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548605331351243167366593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6796280883603315112977581 2548605331351243167366593)
  ·
    refine ⟨1911453998513432375524945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2548605331351243167366593 1911453998513432375524945)
    ·
      refine ⟨1433590498885074281643709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1911453998513432375524945 1433590498885074281643709)
      ·
        refine ⟨537596437081902855616391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1433590498885074281643709 537596437081902855616391)
        ·
          refine ⟨806394655622854283424587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537596437081902855616391 806394655622854283424587)
          ·
            refine ⟨1209591983434281425136881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806394655622854283424587 1209591983434281425136881)
            ·
              refine ⟨907193987575711068852661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209591983434281425136881 907193987575711068852661)
              ·
                refine ⟨85049436335222912704937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 907193987575711068852661 85049436335222912704937)
                ·
                  rfl

theorem cell19_279506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_279506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279506 prefixEnd_279506 := by exact prefixLift 279506
  have htrace : WordTrace (prefixWord ++ tailWord_279506) baseStart_279506 baseEnd_279506 := by
    simpa [prefixWord, tailWord_279506, baseEnd_279506] using wordTrace_append hprefix tailTrace_279506
  have hstable : (prefixWord ++ tailWord_279506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279506).length < 2 ^ (prefixWord ++ tailWord_279506).sum := by decide
  have hdescent : baseEnd_279506 < baseStart_279506 := by decide
  rcases family_descends (prefixWord ++ tailWord_279506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279525 : List Nat := [1, 3, 1, 6, 1, 7]
def baseStart_279525 : Nat := 118140960795 + 279525 * 2 ^ 59
def prefixEnd_279525 : Nat := 4983230072969 + 3 ^ 40 * 279525 * 2
def baseEnd_279525 : Nat := 9450579749670722031407

theorem tailTrace_279525 : CollatzResearch.WordTrace tailWord_279525 prefixEnd_279525 9450579749670722031407 := by
  unfold tailWord_279525
  simp only [CollatzResearch.WordTrace]
  refine ⟨10195114312336138914408029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6796742874890759276272019 10195114312336138914408029)
  ·
    refine ⟨3823167867126052092903011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10195114312336138914408029 3823167867126052092903011)
    ·
      refine ⟨5734751800689078139354517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823167867126052092903011 5734751800689078139354517)
      ·
        refine ⟨268816490657300537782243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5734751800689078139354517 268816490657300537782243)
        ·
          refine ⟨403224735985950806673365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268816490657300537782243 403224735985950806673365)
          ·
            refine ⟨9450579749670722031407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 403224735985950806673365 9450579749670722031407)
            ·
              rfl

theorem cell19_279525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_279525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279525 prefixEnd_279525 := by exact prefixLift 279525
  have htrace : WordTrace (prefixWord ++ tailWord_279525) baseStart_279525 baseEnd_279525 := by
    simpa [prefixWord, tailWord_279525, baseEnd_279525] using wordTrace_append hprefix tailTrace_279525
  have hstable : (prefixWord ++ tailWord_279525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279525).length < 2 ^ (prefixWord ++ tailWord_279525).sum := by decide
  have hdescent : baseEnd_279525 < baseStart_279525 := by decide
  rcases family_descends (prefixWord ++ tailWord_279525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279527 : List Nat := [1, 1, 5, 2, 2, 8]
def baseStart_279527 : Nat := 118140960795 + 279527 * 2 ^ 59
def prefixEnd_279527 : Nat := 4983230072969 + 3 ^ 40 * 279527 * 2
def baseEnd_279527 : Nat := 9450647368522342915357

theorem tailTrace_279527 : CollatzResearch.WordTrace tailWord_279527 prefixEnd_279527 9450647368522342915357 := by
  unfold tailWord_279527
  simp only [CollatzResearch.WordTrace]
  refine ⟨10195187258328893255980835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6796791505552595503987223 10195187258328893255980835)
  ·
    refine ⟨15292780887493339883971253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10195187258328893255980835 15292780887493339883971253)
    ·
      refine ⟨1433698208202500614122305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15292780887493339883971253 1433698208202500614122305)
      ·
        refine ⟨1075273656151875460591729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1433698208202500614122305 1075273656151875460591729)
        ·
          refine ⟨806455242113906595443797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075273656151875460591729 806455242113906595443797)
          ·
            refine ⟨9450647368522342915357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 806455242113906595443797 9450647368522342915357)
            ·
              rfl

theorem cell19_279527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_279527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279527 prefixEnd_279527 := by exact prefixLift 279527
  have htrace : WordTrace (prefixWord ++ tailWord_279527) baseStart_279527 baseEnd_279527 := by
    simpa [prefixWord, tailWord_279527, baseEnd_279527] using wordTrace_append hprefix tailTrace_279527
  have hstable : (prefixWord ++ tailWord_279527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279527).length < 2 ^ (prefixWord ++ tailWord_279527).sum := by decide
  have hdescent : baseEnd_279527 < baseStart_279527 := by decide
  rcases family_descends (prefixWord ++ tailWord_279527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279542 : List Nat := [5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_279542 : Nat := 118140960795 + 279542 * 2 ^ 59
def prefixEnd_279542 : Nat := 4983230072969 + 3 ^ 40 * 279542 * 2
def baseEnd_279542 : Nat := 85060390589185495904839

theorem tailTrace_279542 : CollatzResearch.WordTrace tailWord_279542 prefixEnd_279542 85060390589185495904839 := by
  unfold tailWord_279542
  simp only [CollatzResearch.WordTrace]
  refine ⟨637233397079659426111055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6797156235516367211851253 637233397079659426111055)
  ·
    refine ⟨955850095619489139166583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 637233397079659426111055 955850095619489139166583)
    ·
      refine ⟨1433775143429233708749875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955850095619489139166583 1433775143429233708749875)
      ·
        refine ⟨2150662715143850563124813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433775143429233708749875 2150662715143850563124813)
        ·
          refine ⟨806498518178943961171805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2150662715143850563124813 806498518178943961171805)
          ·
            refine ⟨302436944317103985439427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806498518178943961171805 302436944317103985439427)
            ·
              refine ⟨453655416475655978159141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302436944317103985439427 453655416475655978159141)
              ·
                refine ⟨85060390589185495904839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453655416475655978159141 85060390589185495904839)
                ·
                  rfl

theorem cell19_279542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_279542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279542 prefixEnd_279542 := by exact prefixLift 279542
  have htrace : WordTrace (prefixWord ++ tailWord_279542) baseStart_279542 baseEnd_279542 := by
    simpa [prefixWord, tailWord_279542, baseEnd_279542] using wordTrace_append hprefix tailTrace_279542
  have hstable : (prefixWord ++ tailWord_279542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279542).length < 2 ^ (prefixWord ++ tailWord_279542).sum := by decide
  have hdescent : baseEnd_279542 < baseStart_279542 := by decide
  rcases family_descends (prefixWord ++ tailWord_279542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279563 : List Nat := [1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_279563 : Nat := 118140960795 + 279563 * 2 ^ 59
def prefixEnd_279563 : Nat := 4983230072969 + 3 ^ 40 * 279563 * 2
def baseEnd_279563 : Nat := 85066780570663669438115

theorem tailTrace_279563 : CollatzResearch.WordTrace tailWord_279563 prefixEnd_279563 85066780570663669438115 := by
  unfold tailWord_279563
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196500286198471404291343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6797666857465647602860895 10196500286198471404291343)
  ·
    refine ⟨15294750429297707106437015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10196500286198471404291343 15294750429297707106437015)
    ·
      refine ⟨22942125643946560659655523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15294750429297707106437015 22942125643946560659655523)
      ·
        refine ⟨34413188465919840989483285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22942125643946560659655523 34413188465919840989483285)
        ·
          refine ⟨1613118209339992546382029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34413188465919840989483285 1613118209339992546382029)
          ·
            refine ⟨604919328502497204893261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1613118209339992546382029 604919328502497204893261)
            ·
              refine ⟨226844748188436451834973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 604919328502497204893261 226844748188436451834973)
              ·
                refine ⟨85066780570663669438115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226844748188436451834973 85066780570663669438115)
                ·
                  rfl

theorem cell19_279563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_279563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279563 prefixEnd_279563 := by exact prefixLift 279563
  have htrace : WordTrace (prefixWord ++ tailWord_279563) baseStart_279563 baseEnd_279563 := by
    simpa [prefixWord, tailWord_279563, baseEnd_279563] using wordTrace_append hprefix tailTrace_279563
  have hstable : (prefixWord ++ tailWord_279563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279563).length < 2 ^ (prefixWord ++ tailWord_279563).sum := by decide
  have hdescent : baseEnd_279563 < baseStart_279563 := by decide
  rcases family_descends (prefixWord ++ tailWord_279563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279656 : List Nat := [2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_279656 : Nat := 118140960795 + 279656 * 2 ^ 59
def prefixEnd_279656 : Nat := 4983230072969 + 3 ^ 40 * 279656 * 2
def baseEnd_279656 : Nat := 85095079060067009371195

theorem tailTrace_279656 : CollatzResearch.WordTrace tailWord_279656 prefixEnd_279656 85095079060067009371195 := by
  unfold tailWord_279656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099946137430774143713411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6799928183241032191617881 5099946137430774143713411)
  ·
    refine ⟨7649919206146161215570117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5099946137430774143713411 7649919206146161215570117)
    ·
      refine ⟨1434359851152405227919397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7649919206146161215570117 1434359851152405227919397)
      ·
        refine ⟨268942472091075980234887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1434359851152405227919397 268942472091075980234887)
        ·
          refine ⟨403413708136613970352331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268942472091075980234887 403413708136613970352331)
          ·
            refine ⟨605120562204920955528497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403413708136613970352331 605120562204920955528497)
            ·
              refine ⟨453840421653690716646373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605120562204920955528497 453840421653690716646373)
              ·
                refine ⟨85095079060067009371195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453840421653690716646373 85095079060067009371195)
                ·
                  rfl

theorem cell19_279656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_279656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279656 prefixEnd_279656 := by exact prefixLift 279656
  have htrace : WordTrace (prefixWord ++ tailWord_279656) baseStart_279656 baseEnd_279656 := by
    simpa [prefixWord, tailWord_279656, baseEnd_279656] using wordTrace_append hprefix tailTrace_279656
  have hstable : (prefixWord ++ tailWord_279656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279656).length < 2 ^ (prefixWord ++ tailWord_279656).sum := by decide
  have hdescent : baseEnd_279656 < baseStart_279656 := by decide
  rcases family_descends (prefixWord ++ tailWord_279656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279658 : List Nat := [3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_279658 : Nat := 118140960795 + 279658 * 2 ^ 59
def prefixEnd_279658 : Nat := 4983230072969 + 3 ^ 40 * 279658 * 2
def baseEnd_279658 : Nat := 85095687629731597326745

theorem tailTrace_279658 : CollatzResearch.WordTrace tailWord_279658 prefixEnd_279658 85095687629731597326745 := by
  unfold tailWord_279658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549991305213575657249907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6799976813902868419333085 2549991305213575657249907)
  ·
    refine ⟨3824986957820363485874861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549991305213575657249907 3824986957820363485874861)
    ·
      refine ⟨1434370109182636307203073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3824986957820363485874861 1434370109182636307203073)
      ·
        refine ⟨1075777581886977230402305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1434370109182636307203073 1075777581886977230402305)
        ·
          refine ⟨806833186415232922801729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075777581886977230402305 806833186415232922801729)
          ·
            refine ⟨605124889811424692101297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806833186415232922801729 605124889811424692101297)
            ·
              refine ⟨453843667358568519075973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605124889811424692101297 453843667358568519075973)
              ·
                refine ⟨85095687629731597326745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453843667358568519075973 85095687629731597326745)
                ·
                  rfl

theorem cell19_279658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_279658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279658 prefixEnd_279658 := by exact prefixLift 279658
  have htrace : WordTrace (prefixWord ++ tailWord_279658) baseStart_279658 baseEnd_279658 := by
    simpa [prefixWord, tailWord_279658, baseEnd_279658] using wordTrace_append hprefix tailTrace_279658
  have hstable : (prefixWord ++ tailWord_279658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279658).length < 2 ^ (prefixWord ++ tailWord_279658).sum := by decide
  have hdescent : baseEnd_279658 < baseStart_279658 := by decide
  rcases family_descends (prefixWord ++ tailWord_279658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279660 : List Nat := [2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_279660 : Nat := 118140960795 + 279660 * 2 ^ 59
def prefixEnd_279660 : Nat := 4983230072969 + 3 ^ 40 * 279660 * 2
def baseEnd_279660 : Nat := 85096296199396185282295

theorem tailTrace_279660 : CollatzResearch.WordTrace tailWord_279660 prefixEnd_279660 85096296199396185282295 := by
  unfold tailWord_279660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100019083423528485286217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6800025444564704647048289 5100019083423528485286217)
  ·
    refine ⟨3825014312567646363964663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5100019083423528485286217 3825014312567646363964663)
    ·
      refine ⟨5737521468851469545946995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3825014312567646363964663 5737521468851469545946995)
      ·
        refine ⟨8606282203277204318920493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5737521468851469545946995 8606282203277204318920493)
        ·
          refine ⟨3227355826228951619595185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8606282203277204318920493 3227355826228951619595185)
          ·
            refine ⟨2420516869671713714696389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3227355826228951619595185 2420516869671713714696389)
            ·
              refine ⟨453846913063446321505573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2420516869671713714696389 453846913063446321505573)
              ·
                refine ⟨85096296199396185282295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453846913063446321505573 85096296199396185282295)
                ·
                  rfl

theorem cell19_279660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_279660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279660 prefixEnd_279660 := by exact prefixLift 279660
  have htrace : WordTrace (prefixWord ++ tailWord_279660) baseStart_279660 baseEnd_279660 := by
    simpa [prefixWord, tailWord_279660, baseEnd_279660] using wordTrace_append hprefix tailTrace_279660
  have hstable : (prefixWord ++ tailWord_279660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279660).length < 2 ^ (prefixWord ++ tailWord_279660).sum := by decide
  have hdescent : baseEnd_279660 < baseStart_279660 := by decide
  rcases family_descends (prefixWord ++ tailWord_279660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279698 : List Nat := [3, 2, 3, 1, 1, 9]
def baseStart_279698 : Nat := 118140960795 + 279698 * 2 ^ 59
def prefixEnd_279698 : Nat := 4983230072969 + 3 ^ 40 * 279698 * 2
def baseEnd_279698 : Nat := 9456428780335928493083

theorem tailTrace_279698 : CollatzResearch.WordTrace tailWord_279698 prefixEnd_279698 9456428780335928493083 := by
  unfold tailWord_279698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550356035177347365113937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6800949427139592973637165 2550356035177347365113937)
  ·
    refine ⟨1912767026383010523835453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2550356035177347365113937 1912767026383010523835453)
    ·
      refine ⟨717287634893628946438295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1912767026383010523835453 717287634893628946438295)
      ·
        refine ⟨1075931452340443419657443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717287634893628946438295 1075931452340443419657443)
        ·
          refine ⟨1613897178510665129486165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075931452340443419657443 1613897178510665129486165)
          ·
            refine ⟨9456428780335928493083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1613897178510665129486165 9456428780335928493083)
            ·
              rfl

theorem cell19_279698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_279698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279698 prefixEnd_279698 := by exact prefixLift 279698
  have htrace : WordTrace (prefixWord ++ tailWord_279698) baseStart_279698 baseEnd_279698 := by
    simpa [prefixWord, tailWord_279698, baseEnd_279698] using wordTrace_append hprefix tailTrace_279698
  have hstable : (prefixWord ++ tailWord_279698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279698).length < 2 ^ (prefixWord ++ tailWord_279698).sum := by decide
  have hdescent : baseEnd_279698 < baseStart_279698 := by decide
  rcases family_descends (prefixWord ++ tailWord_279698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279717 : List Nat := [1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_279717 : Nat := 118140960795 + 279717 * 2 ^ 59
def prefixEnd_279717 : Nat := 4983230072969 + 3 ^ 40 * 279717 * 2
def baseEnd_279717 : Nat := 85113640434836942015473

theorem tailTrace_279717 : CollatzResearch.WordTrace tailWord_279717 prefixEnd_279717 85113640434836942015473 := by
  unfold tailWord_279717
  simp only [CollatzResearch.WordTrace]
  refine ⟨10202117127640555705397405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6801411418427037136931603 10202117127640555705397405)
  ·
    refine ⟨3825793922865208389524027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10202117127640555705397405 3825793922865208389524027)
    ·
      refine ⟨5738690884297812584286041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3825793922865208389524027 5738690884297812584286041)
      ·
        refine ⟨4304018163223359438214531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5738690884297812584286041 4304018163223359438214531)
        ·
          refine ⟨6456027244835039157321797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304018163223359438214531 6456027244835039157321797)
          ·
            refine ⟨1210505108406569841997837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6456027244835039157321797 1210505108406569841997837)
            ·
              refine ⟨453939415652463690749189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210505108406569841997837 453939415652463690749189)
              ·
                refine ⟨85113640434836942015473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453939415652463690749189 85113640434836942015473)
                ·
                  rfl

theorem cell19_279717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_279717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279717 prefixEnd_279717 := by exact prefixLift 279717
  have htrace : WordTrace (prefixWord ++ tailWord_279717) baseStart_279717 baseEnd_279717 := by
    simpa [prefixWord, tailWord_279717, baseEnd_279717] using wordTrace_append hprefix tailTrace_279717
  have hstable : (prefixWord ++ tailWord_279717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279717).length < 2 ^ (prefixWord ++ tailWord_279717).sum := by decide
  have hdescent : baseEnd_279717 < baseStart_279717 := by decide
  rcases family_descends (prefixWord ++ tailWord_279717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279789 : List Nat := [1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_279789 : Nat := 118140960795 + 279789 * 2 ^ 59
def prefixEnd_279789 : Nat := 4983230072969 + 3 ^ 40 * 279789 * 2
def baseEnd_279789 : Nat := 85135548942762108415277

theorem tailTrace_279789 : CollatzResearch.WordTrace tailWord_279789 prefixEnd_279789 85135548942762108415277 := by
  unfold tailWord_279789
  simp only [CollatzResearch.WordTrace]
  refine ⟨10204743183379712002018421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6803162122253141334678947 10204743183379712002018421)
  ·
    refine ⟨956694673441848000189227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10204743183379712002018421 956694673441848000189227)
    ·
      refine ⟨1435042010162772000283841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956694673441848000189227 1435042010162772000283841)
      ·
        refine ⟨1076281507622079000212881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1435042010162772000283841 1076281507622079000212881)
        ·
          refine ⟨807211130716559250159661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076281507622079000212881 807211130716559250159661)
          ·
            refine ⟨302704174018709718809873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 807211130716559250159661 302704174018709718809873)
            ·
              refine ⟨227028130514032289107405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302704174018709718809873 227028130514032289107405)
              ·
                refine ⟨85135548942762108415277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227028130514032289107405 85135548942762108415277)
                ·
                  rfl

theorem cell19_279789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_279789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279789 prefixEnd_279789 := by exact prefixLift 279789
  have htrace : WordTrace (prefixWord ++ tailWord_279789) baseStart_279789 baseEnd_279789 := by
    simpa [prefixWord, tailWord_279789, baseEnd_279789] using wordTrace_append hprefix tailTrace_279789
  have hstable : (prefixWord ++ tailWord_279789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279789).length < 2 ^ (prefixWord ++ tailWord_279789).sum := by decide
  have hdescent : baseEnd_279789 < baseStart_279789 := by decide
  rcases family_descends (prefixWord ++ tailWord_279789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279812 : List Nat := [2, 3, 2, 2, 2, 1, 7]
def baseStart_279812 : Nat := 118140960795 + 279812 * 2 ^ 59
def prefixEnd_279812 : Nat := 4983230072969 + 3 ^ 40 * 279812 * 2
def baseEnd_279812 : Nat := 28380849164634956634701

theorem tailTrace_279812 : CollatzResearch.WordTrace tailWord_279812 prefixEnd_279812 28380849164634956634701 := by
  unfold tailWord_279812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102791031148193465052845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6803721374864257953403793 5102791031148193465052845)
  ·
    refine ⟨1913546636680572549394817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5102791031148193465052845 1913546636680572549394817)
    ·
      refine ⟨1435159977510429412046113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1913546636680572549394817 1435159977510429412046113)
      ·
        refine ⟨1076369983132822059034585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1435159977510429412046113 1076369983132822059034585)
        ·
          refine ⟨807277487349616544275939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076369983132822059034585 807277487349616544275939)
          ·
            refine ⟨1210916231024424816413909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807277487349616544275939 1210916231024424816413909)
            ·
              refine ⟨28380849164634956634701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1210916231024424816413909 28380849164634956634701)
              ·
                rfl

theorem cell19_279812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_279812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279812 prefixEnd_279812 := by exact prefixLift 279812
  have htrace : WordTrace (prefixWord ++ tailWord_279812) baseStart_279812 baseEnd_279812 := by
    simpa [prefixWord, tailWord_279812, baseEnd_279812] using wordTrace_append hprefix tailTrace_279812
  have hstable : (prefixWord ++ tailWord_279812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279812).length < 2 ^ (prefixWord ++ tailWord_279812).sum := by decide
  have hdescent : baseEnd_279812 < baseStart_279812 := by decide
  rcases family_descends (prefixWord ++ tailWord_279812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279831 : List Nat := [1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_279831 : Nat := 118140960795 + 279831 * 2 ^ 59
def prefixEnd_279831 : Nat := 4983230072969 + 3 ^ 40 * 279831 * 2
def baseEnd_279831 : Nat := 85148328905718455481829

theorem tailTrace_279831 : CollatzResearch.WordTrace tailWord_279831 prefixEnd_279831 85148328905718455481829 := by
  unfold tailWord_279831
  simp only [CollatzResearch.WordTrace]
  refine ⟨10206275049227553175047347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6804183366151702116698231 10206275049227553175047347)
  ·
    refine ⟨15309412573841329762571021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10206275049227553175047347 15309412573841329762571021)
    ·
      refine ⟨5741029715190498660964133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15309412573841329762571021 5741029715190498660964133)
      ·
        refine ⟨1076443071598218498930775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5741029715190498660964133 1076443071598218498930775)
        ·
          refine ⟨1614664607397327748396163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076443071598218498930775 1614664607397327748396163)
          ·
            refine ⟨2421996911095991622594245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614664607397327748396163 2421996911095991622594245)
            ·
              refine ⟨454124420830498429236421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2421996911095991622594245 454124420830498429236421)
              ·
                refine ⟨85148328905718455481829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454124420830498429236421 85148328905718455481829)
                ·
                  rfl

theorem cell19_279831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_279831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279831 prefixEnd_279831 := by exact prefixLift 279831
  have htrace : WordTrace (prefixWord ++ tailWord_279831) baseStart_279831 baseEnd_279831 := by
    simpa [prefixWord, tailWord_279831, baseEnd_279831] using wordTrace_append hprefix tailTrace_279831
  have hstable : (prefixWord ++ tailWord_279831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279831).length < 2 ^ (prefixWord ++ tailWord_279831).sum := by decide
  have hdescent : baseEnd_279831 < baseStart_279831 := by decide
  rcases family_descends (prefixWord ++ tailWord_279831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279869 : List Nat := [1, 4, 1, 5, 8]
def baseStart_279869 : Nat := 118140960795 + 279869 * 2 ^ 59
def prefixEnd_279869 : Nat := 4983230072969 + 3 ^ 40 * 279869 * 2
def baseEnd_279869 : Nat := 3154070064049838023603

theorem tailTrace_279869 : CollatzResearch.WordTrace tailWord_279869 prefixEnd_279869 3154070064049838023603 := by
  unfold tailWord_279869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207661023089885664930661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6805107348726590443287107 10207661023089885664930661)
  ·
    refine ⟨1913936441829353562174499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10207661023089885664930661 1913936441829353562174499)
    ·
      refine ⟨2870904662744030343261749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913936441829353562174499 2870904662744030343261749)
      ·
        refine ⟨269147312132252844680789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2870904662744030343261749 269147312132252844680789)
        ·
          refine ⟨3154070064049838023603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 269147312132252844680789 3154070064049838023603)
          ·
            rfl

theorem cell19_279869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 8].length) (baseStart_279869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279869 prefixEnd_279869 := by exact prefixLift 279869
  have htrace : WordTrace (prefixWord ++ tailWord_279869) baseStart_279869 baseEnd_279869 := by
    simpa [prefixWord, tailWord_279869, baseEnd_279869] using wordTrace_append hprefix tailTrace_279869
  have hstable : (prefixWord ++ tailWord_279869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279869).length < 2 ^ (prefixWord ++ tailWord_279869).sum := by decide
  have hdescent : baseEnd_279869 < baseStart_279869 := by decide
  rcases family_descends (prefixWord ++ tailWord_279869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279871 : List Nat := [1, 1, 2, 2, 4, 9]
def baseStart_279871 : Nat := 118140960795 + 279871 * 2 ^ 59
def prefixEnd_279871 : Nat := 4983230072969 + 3 ^ 40 * 279871 * 2
def baseEnd_279871 : Nat := 9462277811001134954759

theorem tailTrace_279871 : CollatzResearch.WordTrace tailWord_279871 prefixEnd_279871 9462277811001134954759 := by
  unfold tailWord_279871
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207733969082640006503467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6805155979388426671002311 10207733969082640006503467)
  ·
    refine ⟨15311600953623960009755201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10207733969082640006503467 15311600953623960009755201)
    ·
      refine ⟨11483700715217970007316401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15311600953623960009755201 11483700715217970007316401)
      ·
        refine ⟨8612775536413477505487301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11483700715217970007316401 8612775536413477505487301)
        ·
          refine ⟨1614895413077527032278869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8612775536413477505487301 1614895413077527032278869)
          ·
            refine ⟨9462277811001134954759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1614895413077527032278869 9462277811001134954759)
            ·
              rfl

theorem cell19_279871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_279871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279871 prefixEnd_279871 := by exact prefixLift 279871
  have htrace : WordTrace (prefixWord ++ tailWord_279871) baseStart_279871 baseEnd_279871 := by
    simpa [prefixWord, tailWord_279871, baseEnd_279871] using wordTrace_append hprefix tailTrace_279871
  have hstable : (prefixWord ++ tailWord_279871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279871).length < 2 ^ (prefixWord ++ tailWord_279871).sum := by decide
  have hdescent : baseEnd_279871 < baseStart_279871 := by decide
  rcases family_descends (prefixWord ++ tailWord_279871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279947 : List Nat := [1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_279947 : Nat := 118140960795 + 279947 * 2 ^ 59
def prefixEnd_279947 : Nat := 4983230072969 + 3 ^ 40 * 279947 * 2
def baseEnd_279947 : Nat := 85183625946264556903735

theorem tailTrace_279947 : CollatzResearch.WordTrace tailWord_279947 prefixEnd_279947 85183625946264556903735 := by
  unfold tailWord_279947
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210505916807304986270095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6807003944538203324180063 10210505916807304986270095)
  ·
    refine ⟨15315758875210957479405143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10210505916807304986270095 15315758875210957479405143)
    ·
      refine ⟨22973638312816436219107715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15315758875210957479405143 22973638312816436219107715)
      ·
        refine ⟨34460457469224654328661573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22973638312816436219107715 34460457469224654328661573)
        ·
          refine ⟨6461335775479622686624045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34460457469224654328661573 6461335775479622686624045)
          ·
            refine ⟨2423000915804858507484017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6461335775479622686624045 2423000915804858507484017)
            ·
              refine ⟨1817250686853643880613013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423000915804858507484017 1817250686853643880613013)
              ·
                refine ⟨85183625946264556903735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1817250686853643880613013 85183625946264556903735)
                ·
                  rfl

theorem cell19_279947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_279947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279947 prefixEnd_279947 := by exact prefixLift 279947
  have htrace : WordTrace (prefixWord ++ tailWord_279947) baseStart_279947 baseEnd_279947 := by
    simpa [prefixWord, tailWord_279947, baseEnd_279947] using wordTrace_append hprefix tailTrace_279947
  have hstable : (prefixWord ++ tailWord_279947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279947).length < 2 ^ (prefixWord ++ tailWord_279947).sum := by decide
  have hdescent : baseEnd_279947 < baseStart_279947 := by decide
  rcases family_descends (prefixWord ++ tailWord_279947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279960 : List Nat := [2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_279960 : Nat := 118140960795 + 279960 * 2 ^ 59
def prefixEnd_279960 : Nat := 4983230072969 + 3 ^ 40 * 279960 * 2
def baseEnd_279960 : Nat := 85187581649084378614811

theorem tailTrace_279960 : CollatzResearch.WordTrace tailWord_279960 prefixEnd_279960 85187581649084378614811 := by
  unfold tailWord_279960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5105490032880104103246667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6807320043840138804328889 5105490032880104103246667)
  ·
    refine ⟨7658235049320156154870001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5105490032880104103246667 7658235049320156154870001)
    ·
      refine ⟨5743676286990117116152501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7658235049320156154870001 5743676286990117116152501)
      ·
        refine ⟨538469651905323479639297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5743676286990117116152501 538469651905323479639297)
        ·
          refine ⟨403852238928992609729473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538469651905323479639297 403852238928992609729473)
          ·
            refine ⟨302889179196744457297105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403852238928992609729473 302889179196744457297105)
            ·
              refine ⟨227166884397558342972829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302889179196744457297105 227166884397558342972829)
              ·
                refine ⟨85187581649084378614811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227166884397558342972829 85187581649084378614811)
                ·
                  rfl

theorem cell19_279960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_279960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279960 prefixEnd_279960 := by exact prefixLift 279960
  have htrace : WordTrace (prefixWord ++ tailWord_279960) baseStart_279960 baseEnd_279960 := by
    simpa [prefixWord, tailWord_279960, baseEnd_279960] using wordTrace_append hprefix tailTrace_279960
  have hstable : (prefixWord ++ tailWord_279960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279960).length < 2 ^ (prefixWord ++ tailWord_279960).sum := by decide
  have hdescent : baseEnd_279960 < baseStart_279960 := by decide
  rcases family_descends (prefixWord ++ tailWord_279960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279981 : List Nat := [1, 5, 2, 2, 1, 3, 5]
def baseStart_279981 : Nat := 118140960795 + 279981 * 2 ^ 59
def prefixEnd_279981 : Nat := 4983230072969 + 3 ^ 40 * 279981 * 2
def baseEnd_279981 : Nat := 28397990543520850716029

theorem tailTrace_279981 : CollatzResearch.WordTrace tailWord_279981 prefixEnd_279981 28397990543520850716029 := by
  unfold tailWord_279981
  simp only [CollatzResearch.WordTrace]
  refine ⟨10211745998684128793007797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6807830665789419195338531 10211745998684128793007797)
  ·
    refine ⟨957351187376637074344481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10211745998684128793007797 957351187376637074344481)
    ·
      refine ⟨718013390532477805758361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 957351187376637074344481 718013390532477805758361)
      ·
        refine ⟨538510042899358354318771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 718013390532477805758361 538510042899358354318771)
        ·
          refine ⟨807765064349037531478157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538510042899358354318771 807765064349037531478157)
          ·
            refine ⟨302911899130889074304309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 807765064349037531478157 302911899130889074304309)
            ·
              refine ⟨28397990543520850716029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 302911899130889074304309 28397990543520850716029)
              ·
                rfl

theorem cell19_279981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_279981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_279981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_279981 prefixEnd_279981 := by exact prefixLift 279981
  have htrace : WordTrace (prefixWord ++ tailWord_279981) baseStart_279981 baseEnd_279981 := by
    simpa [prefixWord, tailWord_279981, baseEnd_279981] using wordTrace_append hprefix tailTrace_279981
  have hstable : (prefixWord ++ tailWord_279981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279981).length < 2 ^ (prefixWord ++ tailWord_279981).sum := by decide
  have hdescent : baseEnd_279981 < baseStart_279981 := by decide
  rcases family_descends (prefixWord ++ tailWord_279981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280042 : List Nat := [3, 1, 3, 1, 11]
def baseStart_280042 : Nat := 118140960795 + 280042 * 2 ^ 59
def prefixEnd_280042 : Nat := 4983230072969 + 3 ^ 40 * 280042 * 2
def baseEnd_280042 : Nat := 3156019740938240177495

theorem tailTrace_280042 : CollatzResearch.WordTrace tailWord_280042 prefixEnd_280042 3156019740938240177495 := by
  unfold tailWord_280042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553492712865784052744595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6809313900975424140652253 2553492712865784052744595)
  ·
    refine ⟨3830239069298676079116893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2553492712865784052744595 3830239069298676079116893)
    ·
      refine ⟨1436339650987003529668835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3830239069298676079116893 1436339650987003529668835)
      ·
        refine ⟨2154509476480505294503253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436339650987003529668835 2154509476480505294503253)
        ·
          refine ⟨3156019740938240177495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2154509476480505294503253 3156019740938240177495)
          ·
            rfl

theorem cell19_280042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 11].length) (baseStart_280042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280042 prefixEnd_280042 := by exact prefixLift 280042
  have htrace : WordTrace (prefixWord ++ tailWord_280042) baseStart_280042 baseEnd_280042 := by
    simpa [prefixWord, tailWord_280042, baseEnd_280042] using wordTrace_append hprefix tailTrace_280042
  have hstable : (prefixWord ++ tailWord_280042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280042).length < 2 ^ (prefixWord ++ tailWord_280042).sum := by decide
  have hdescent : baseEnd_280042 < baseStart_280042 := by decide
  rcases family_descends (prefixWord ++ tailWord_280042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
